////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Split structures to constituent signals
//   - Does not update instance port selects
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable

final class SplitStructsA(implicit cc: CompilerContext) extends TreeTransformer {

  private[this] val fieldIndexStack = mutable.Stack[Int]()

  private[this] def flattenStruct(prefix: String, kind: TypeRecord): List[(String, TypeFund)] = {
    kind.publicSymbols flatMap { symbol =>
      symbol.kind match {
        case k: TypeRecord   => flattenStruct(s"$prefix${cc.sep}${symbol.name}", k)
        case other: TypeFund => List((s"$prefix${cc.sep}${symbol.name}", other))
        case _               => ???
      }
    }
  }

  override def enter(tree: Tree): Unit = tree match {
    case Decl(Sym(eSymbol, _), desc: DescEntity) =>
      if (!eSymbol.attr.highLevelKind.isSet) {
        cc.ice(eSymbol, s"Missing highLevelKind attribute on entity ${eSymbol.name}")
      }

      for (Decl(Sym(symbol, _), _) <- desc.decls) {
        symbol.kind.underlying match {
          case struct: TypeRecord =>
            val newSymbols = for ((fName, fKind) <- flattenStruct(symbol.name, struct)) yield {
              val nKind = symbol.kind match {
                case k: TypeIn     => k.copy(kind = fKind)
                case k: TypeOut    => k.copy(kind = fKind)
                case k: TypeConst  => k.copy(kind = fKind)
                case _: TypeRecord => fKind
                case _             => unreachable
              }
              cc.newSymbol(fName, symbol.loc) tap { _.kind = nKind }
            }
            val widths = newSymbols map { _.kind.width }
            val offsets = widths.scanLeft(BigInt(0))(_ + _)
            // TODO: rewrite with loop() ...
            for ((newSymbol, offset) <- newSymbols zip offsets) {
              newSymbol.attr.fieldOffset set offset.toInt
              newSymbol.attr.structSymbol set symbol
            }
            symbol.attr.fieldSymbols set newSymbols
          case _ => ()
        }
      }

      // Transfer the oReg attributes
      for {
        Decl(Sym(symbol, _), _) <- desc.decls
        if symbol.attr.fieldSymbols.isSet
        rSymbol <- symbol.attr.oReg.get
      } {
        val oFieldSymbols = symbol.attr.fieldSymbols.value
        val rFieldSymbols = rSymbol.attr.fieldSymbols.value
        for ((oFieldSymbol, rFieldSymbol) <- oFieldSymbols zip rFieldSymbols) {
          oFieldSymbol.attr.oReg set rFieldSymbol
        }
      }

    case ExprSelect(expr, sel, _) =>
      expr.tpe.underlying match {
        case kind: TypeRecord => fieldIndexStack push kind.publicSymbols.indexWhere(_.name == sel)
        case _                => fieldIndexStack push -1
      }

    case _ => ()
  }

  private[this] def fieldDecls(fSymbols: List[Symbol], initOpt: Option[Expr]): List[EntDecl] = {
    initOpt match {
      case Some(init) =>
        val widths = fSymbols map { _.kind.width }
        val lsbs = widths.scanRight(BigInt(0))(_ + _).tail
        List from {
          for ((symbol, lsb, width) <- fSymbols lazyZip lsbs lazyZip widths) yield {
            val msb = lsb + width - 1
            val expr = ExprSlice(init, Expr(msb), ":", Expr(lsb)) regularize init.loc
            // TODO: teach simplify to simplify more things as necessary
            EntDecl(symbol.decl(expr.simplify))
          }
        }
      case None =>
        fSymbols map { symbol =>
          EntDecl(symbol.decl)
        }
    }
  }

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // ExprSym
      //////////////////////////////////////////////////////////////////////////

      case ExprSym(symbol) =>
        // Rewrite reference to struct symbol as a nested
        // concatenation of references to the field symbols
        symbol.attr.fieldSymbols.get map { fSymbols =>
          def cat(struct: TypeRecord)(implicit it: Iterator[Symbol]): ExprCat = ExprCat {
            for (symbol <- struct.publicSymbols) yield {
              symbol.kind match {
                case struct: TypeRecord => cat(struct)
                case _                  => ExprSym(it.next())
              }
            }
          }
          cat(symbol.kind.underlying.asRecord)(fSymbols.iterator)
        } getOrElse {
          tree
        }

      //////////////////////////////////////////////////////////////////////////
      // ExprSelect
      //////////////////////////////////////////////////////////////////////////

      case ExprSelect(expr, _, _) => {
        if (fieldIndexStack.top >= 0) {
          expr match {
            case ExprCat(parts) => parts(fieldIndexStack.top)
            case _              => tree
          }
        } else {
          tree
        }
      } tap { _ =>
        fieldIndexStack.pop()
      }

      //////////////////////////////////////////////////////////////////////////
      // Drop all record definitions
      //////////////////////////////////////////////////////////////////////////

      case RizDecl(Decl(_, _: DescRecord))  => Thicket(Nil) regularize tree.loc
      case EntDecl(Decl(_, _: DescRecord))  => Thicket(Nil) regularize tree.loc
      case RecDecl(Decl(_, _: DescRecord))  => Thicket(Nil) regularize tree.loc
      case StmtDecl(Decl(_, _: DescRecord)) => Thicket(Nil) regularize tree.loc

      //////////////////////////////////////////////////////////////////////////
      // Decl
      //////////////////////////////////////////////////////////////////////////

      case decl @ EntDecl(Decl(Sym(symbol, _), desc)) =>
        // Add field declarations
        symbol.attr.fieldSymbols.get map { fSymbols =>
          val fDecls = fieldDecls(fSymbols, desc.initializer)
          // Keep original declarations of ports. These are used to resolve
          // inter-entity connections in a second pass
          symbol.kind match {
            case _: TypeIn  => Thicket(decl :: fDecls) regularize tree.loc
            case _: TypeOut => Thicket(decl :: fDecls) regularize tree.loc
            case _          => Thicket(fDecls) regularize tree.loc
          }
        } getOrElse {
          tree
        }

      //////////////////////////////////////////////////////////////////////////
      // Entity
      //////////////////////////////////////////////////////////////////////////

      case _ => tree
    }

    // If we did modify the node, regularize it
    if (result ne tree) {
      result regularize tree.loc
    }

    // Done
    result
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(fieldIndexStack.isEmpty)
  }

}

object SplitStructsA extends TreeTransformerPass {
  val name = "split-structs-a"
  def create(implicit cc: CompilerContext) = new SplitStructsA
}
