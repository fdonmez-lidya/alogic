////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018-2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Symbol representation and creation
////////////////////////////////////////////////////////////////////////////////

// A Symbol is a unique handle to the definition of a Name

package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.util.SequenceNumbers

import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.chaining._

trait Symbols extends { self: CompilerContext =>

  // TODO: review this whole globalScope design..

  // The global scope only holds file level entity symbols
  final private[this] var _globalScope: Option[mutable.HashMap[String, Symbols.Symbol]] =
    Some(mutable.HashMap())

  // Can only hand out the final immutable copy
  final lazy val globalScope: Map[String, Symbols.Symbol] = {
    _globalScope.get.toMap
  } tap { _ =>
    _globalScope = None
  }

  // Add a symbol to the global scope, assuming it is still open
  final def addGlobalSymbol(symbol: Symbols.Symbol): Unit = synchronized {
    _globalScope match {
      case None => ice("Global scope is already sealed")
      case Some(scope) =>
        val name = symbol.name
        if (scope contains name) {
          ice(s"Global scope already contains '$name'")
        }
        scope(name) = symbol
    }
  }

  final def addGlobalDecls(decls: Iterable[Decl]): Unit = synchronized {
    for (decl <- decls) {
      addGlobalSymbol(newSymbol(decl.ref.asInstanceOf[Ident]))
    }

    // Force value to seal global scope
    globalScope
  }

  final def addGlobalDecl(decl: Decl): Unit = addGlobalDecls(List(decl))

  final def lookupGlobalTerm(name: String): Symbols.Symbol = synchronized {
    globalScope.get(name) match {
      case Some(symbol) => symbol
      case None         => ice(s"Cannot find global term '$name'")
    }
  }

  final def makeBuiltinCall(name: String, loc: Loc, args: List[Expr]): ExprCall = {
    val polySymbol = lookupGlobalTerm(name)
    assert(polySymbol.isBuiltin(this))
    assert(args exists { _.hasTpe })
    val argps = args map { a =>
      ArgP(a).regularize(a.loc)(this)
    }
    val symbol = polySymbol.kind(this).asPolyFunc.resolve(argps).get
    val call = ExprSym(symbol).call(argps)(this)
    call.regularize(loc)(this)
  }

  final private[this] val symbolSequenceNumbers = new SequenceNumbers

  //////////////////////////////////////////////////////////////////////////////
  // Creating Symbol instances
  //////////////////////////////////////////////////////////////////////////////

  final def newSymbol(name: String, loc: Loc): Symbols.Symbol = synchronized {
    new Symbols.Symbol(symbolSequenceNumbers.next, loc, name)
  }

  final def newSymbol(ident: Ident): Symbols.Symbol = {
    newSymbol(ident.name, ident.loc) tap { symbol =>
      symbol.attr.update(ident.attr)(this)
    }
  }

  final def newSymbolLike(symbol: Symbols.Symbol): Symbols.Symbol = {
    newSymbol(symbol.name, symbol.loc) tap { newSymbol =>
      newSymbol.kind = symbol.kind(this)
      newSymbol.attr.update(symbol.attr)
    }
  }

}

object Symbols {

  final class Symbol(
      val id: Int,
      val loc: Loc,
      initialName: String
  ) {
    var name: String = initialName

    val attr: SymbolAttributes = new SymbolAttributes()

    def isBuiltin(implicit cc: CompilerContext): Boolean = cc.builtins exists { _ contains this }

    override def hashCode: Int = id // TODO: review if this is still needed

    override def toString = s"Symbol(id=$id, name=$name)"

    ////////////////////////////////////////////////////////////////////////////
    // The following is the mechanism figuring out the type of the symbol
    ////////////////////////////////////////////////////////////////////////////

    // The Decl node introducing this symbol
    private[this] var _decl: Decl = _

    // Setting the Decl invalidates the cached type of the symbol
    def decl_=(decl: Decl): Unit = {
      _kind = TypeUnknown
      _decl = decl
    }

    // If the _decl is known, return it, otherwise fabricate one. Note that
    // creating the Decl node below also has the side effect of setting _decl
    // to that node
    def decl(implicit cc: CompilerContext): Decl =
      if (_decl != null) _decl else Decl(Sym(this, Nil), kind.desc)

    // Create Decl node with given initializier. _decl must be unset
    def decl(init: Expr)(implicit cc: CompilerContext): Decl = {
      assert(_decl == null)
      Decl(Sym(this, Nil), kind.desc(init))
    }

    // Create Decl node with given optional initializier. _decl must be unset
    def decl(init: Option[Expr])(implicit cc: CompilerContext): Decl = {
      assert(_decl == null)
      Decl(Sym(this, Nil), kind.desc(init))
    }

    // Marker for detecting circular definitions
    private[this] var pending: Boolean = false

    // The computed type of the symbol
    private[this] var _kind: Type = TypeUnknown

    // Explicitly setting the type removes the associated Decl node
    def kind_=(kind: Type): Unit = {
      _kind = kind
      _decl = null
    }

    // The type of this symbol. Retrieving this will attempt to compute the
    // type if it is not known, but it might still be unknown if referenced
    // choice symbols have not yet been resolved or if the definition is
    // circular.
    def kind(implicit cc: CompilerContext): Type = {
      // Attempt to compute the type if it is unknown, and we are not already
      // trying to compute it. The latter can arise from circular definitions.
      if (_kind == TypeUnknown && !pending) {
        assert(_decl != null)
        // Mark pending
        pending = true
        // Compute the type of the symbol
        _kind = if (isParametrized) TypeParametrized(this) else computeType
        // Mark complete
        pending = false
      }
      _kind
    }

    private[this] def computeType(implicit cc: CompilerContext): Type = {
      def typeCheck(trees: Tree*)(f: => Option[Type]): Type = {
        val checks = trees flatMap cc.typeCheck
        if (checks exists { !_ }) {
          TypeError
        } else if (checks.length != trees.length) {
          TypeUnknown
        } else {
          f getOrElse TypeError
        }
      }

      def toType(expr: Expr): Option[TypeFund] = expr.tpe match {
        case TypeType(kind) => Some(kind)
        case _              => cc.error(expr, "Expression does not name a type"); None
      }

      def toValue(expr: Expr): Option[BigInt] = expr.value tap {
        case None => cc.error(expr, "Expression must be a compile time constant")
        case _    =>
      }

      def toTypeValue(spec: Expr, expr: Expr): Option[(TypeFund, BigInt)] = {
        toType(spec) flatMap { t =>
          toValue(expr) map { v =>
            (t, v)
          }
        }
      }

      def checkSymbols(symbols: List[Symbol])(f: List[Symbol] => Type): Type = {
        @tailrec
        def loop(ss: List[Symbol]): Type = ss match {
          case head :: tail =>
            head.kind match {
              case TypeError     => TypeError
              case TypeUnknown   => TypeUnknown
              case _: TypeChoice => TypeUnknown
              case _             => loop(tail)
            }
          case Nil => f(symbols)
        }

        loop(symbols)
      }

      // Figure out the type based on the description
      _decl.desc match {
        case DescVar(spec, _) => typeCheck(spec) { toType(spec) }

        case DescIn(spec, fc) => typeCheck(spec) { toType(spec) map { TypeIn(_, fc) } }

        case DescOut(spec, fc, st, _) => typeCheck(spec) { toType(spec) map { TypeOut(_, fc, st) } }

        case DescPipeline(spec) => typeCheck(spec) { toType(spec) map { TypePipeline } }

        case DescParam(spec, _) => typeCheck(spec) { toType(spec) map { TypeParam } }

        case DescConst(spec, _) => typeCheck(spec) { toType(spec) map { TypeConst } }

        case DescGen(spec, _) => typeCheck(spec) { toType(spec) map { TypeGen } }

        case DescArray(elem, size) =>
          typeCheck(elem, size) { toTypeValue(elem, size) map { case (t, v) => TypeArray(t, v) } }

        case DescSram(elem, size, s) =>
          typeCheck(elem, size) { toTypeValue(elem, size) map { case (t, v) => TypeSram(t, v, s) } }

        case DescStack(elem, size) =>
          typeCheck(elem, size) { toTypeValue(elem, size) map { case (t, v) => TypeStack(t, v) } }

        case DescType(spec) => typeCheck(spec) { toType(spec) map TypeType }

        case desc: DescEntity =>
          checkSymbols(desc.publicSymbols) { ss =>
            TypeType(TypeEntity(this, ss))
          }

        case desc: DescRecord =>
          checkSymbols(desc.publicSymbols) { ss =>
            TypeType(TypeRecord(this, ss))
          }

        case DescInstance(spec) =>
          typeCheck(spec) {
            toType(spec)
          } tap {
            case _: TypeEntity => // Ok
            case TypeUnknown   => // Ok
            case _             => cc.error(spec, s"Expression does not name an entity")
          }

        case desc: DescSingleton =>
          checkSymbols(desc.publicSymbols) { ss =>
            TypeEntity(this, ss)
          }

        case DescFunc(variant, ret, args, _) =>
          typeCheck(ret) {
            toType(ret) map { retType =>
              val argSymbols = args map { _.symbol }
              checkSymbols(argSymbols) { ss =>
                val argTypes = ss map { _.kind.asFund }
                variant match {
                  case FuncVariant.Ctrl => TypeCtrlFunc(this, retType, argTypes)
                  case FuncVariant.Comb => TypeCombFunc(this, retType, argTypes)
                  case FuncVariant.None => cc.ice(_decl, "Unknown function variant")
                }
              }
            }
          }

        case _: DescState => TypeState

        case DescChoice(choices) => TypeChoice(choices map { _.symbol })
      }
    }

    def isChoice(implicit cc: CompilerContext): Boolean =
      !isBuiltin && _decl.desc.isInstanceOf[DescChoice]

    ////////////////////////////////////////////////////////////////////////////
    // Things derived from the definition of the symbol
    ////////////////////////////////////////////////////////////////////////////

    // Extract the initializer value from the definition, if any
    def init(implicit cc: CompilerContext): Option[Expr] = {
      if (_decl.desc.initializer.isEmpty) {
        None
      } else if (!_decl.hasTpe && !(cc.typeCheck(_decl) contains true)) {
        None
      } else {
        _decl.normalize.desc.initializer
      }
    }

    def isParametrized(implicit cc: CompilerContext): Boolean = !isBuiltin && {
      assert(_decl != null, _kind.toString + " " + toString)
      _decl.desc.isParametrized
    }

    ////////////////////////////////////////////////////////////////////////////
    // Clone symbol (create new symbol with same name, loc and attributes)
    ////////////////////////////////////////////////////////////////////////////

    def dup(implicit cc: CompilerContext): Symbol =
      cc.newSymbol(name, loc) tap { _.attr update attr }

  }

}
