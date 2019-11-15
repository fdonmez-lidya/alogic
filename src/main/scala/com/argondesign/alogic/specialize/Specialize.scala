////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Specialize parameters and process 'gen' constructs
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.specialize

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.io.AnsiColor

class Specialize(implicit cc: CompilerContext) { self =>

  // Cache of 'original symbol' -> 'bindings' -> 'specialized definition',
  // where the specialized definition might be None if the given bindings
  // are invalid
  private[this] val cache = mutable.HashMap[Symbol, mutable.Map[Map[String, Expr], Option[Decl]]]()

  // To detect circular and divergent definitions, we keep track of the pending
  // specializations on a stack. To avoid having to do a linear time search of
  // the stack all the time, and to provide better error messages, we also keep
  // a map holding the same keys as the stack, with the source location of the
  // reference causing the specialization as the value.
  private[this] val pendingStack = mutable.Stack[(Symbol, Map[String, Expr])]()
  private[this] val pendingMap = mutable.HashMap[(Symbol, Map[String, Expr]), Loc]()

  private[this] def dump(label: String)(decl: Decl): Unit = {
//    val prefix = " " * (4 * (pendingMap.size - 1)) + "|"
//    println(prefix + "------ " + label)
//    println(prefix + decl.toSource.replace("\n", "\n" + prefix))
//    if (cc.hasError) {
//      cc.messages foreach { msg =>
//        println(msg.string)
//      }
//      cc.fatal("Stopping due to errors")
//    }
  }

  private[this] val specialized = mutable.HashSet[Symbol]()

  @tailrec
  private[this] def specialize(
      decl: Decl,
      paramBindings: Map[String, Expr],
      loc: Loc
  ): Option[Decl] = {
    require(!specialized(decl.symbol))

    dump("Input")(decl)

    ////////////////////////////////////////////////////////////////////////////
    // Substitute parameters with the given expression
    ////////////////////////////////////////////////////////////////////////////

    val (substituted: Option[Decl], unusedBindings: Map[String, Expr]) =
      Substitute(decl, paramBindings) match {
        case Left(unbound) =>
          unbound foreach { d: Decl =>
            cc.error(loc, s"'${decl.name}' requires parameter '${d.name}")
          }
          (None, Map.empty[String, Expr])
        case Right((d, unused)) =>
          (Some(d), unused)
      }

    substituted foreach dump("Substituted")

    ////////////////////////////////////////////////////////////////////////////
    // Expand 'gen' constructs
    ////////////////////////////////////////////////////////////////////////////

    val expanded: Option[Decl] = substituted flatMap { decl =>
      Generate(decl)
    }

    expanded foreach dump("Generated")

    ////////////////////////////////////////////////////////////////////////////
    // Specialize every non-parametrized definition required for computing the
    // types of this symbol and of symbols defined within this definition
    ////////////////////////////////////////////////////////////////////////////

    expanded foreach { decl =>
      require(!decl.desc.isParametrized)

      // The list of symbols required to work out the type of the symbol defined
      // by the given definition, together with their referenced location.
      def typingDependencies(decl: Decl): List[(Symbol, Loc)] = {
        def gather(trees: Tree*): List[(Symbol, Loc)] = List from {
          trees.iterator flatMap {
            _ collect {
              case node @ ExprSym(symbol) if !symbol.isBuiltin => (symbol, node.loc)
              case _: ExprRef                                  => unreachable
            }
          }
        }

        decl.desc match {
          case DescVar(spec, _)        => gather(spec)
          case DescIn(spec, _)         => gather(spec)
          case DescOut(spec, _, _, _)  => gather(spec)
          case DescPipeline(spec)      => gather(spec)
          case _: DescParam            => unreachable
          case DescConst(spec, _)      => gather(spec)
          case DescGen(spec, _)        => gather(spec)
          case DescArray(elem, size)   => gather(elem, size)
          case DescSram(elem, size, _) => gather(elem, size)
          case DescStack(elem, size)   => gather(elem, size)
          case DescType(spec)          => gather(spec)
          case desc: DescEntity =>
            desc.publicSymbols map { s =>
              (s, s.loc)
            }
          case desc: DescRecord =>
            desc.publicSymbols map { s =>
              (s, s.loc)
            }
          case DescInstance(spec) => gather(spec)
          case desc: DescSingleton =>
            desc.publicSymbols map { s =>
              (s, s.loc)
            }
          case DescFunc(_, ret, args, _) =>
            gather(ret) ::: (args map { d =>
              (d.symbol, d.symbol.loc)
            })
          case _: DescState  => unreachable
          case _: DescChoice => unreachable
        }
      }

      // Specialize typing dependencies of this symbol
      typingDependencies(decl) filter {
        case (symbol, _) => !symbol.isParametrized && !specialized(symbol)
      } foreach {
        case (symbol, loc) => self(symbol.decl, Map.empty, loc)
      }

      // specialize typing dependencies of symbols introduced
      decl.desc.decls filter { d =>
        !d.symbol.isParametrized && !specialized(d.symbol)
      } foreach { nestedDecl =>
        typingDependencies(nestedDecl) filter {
          case (symbol, _) => !symbol.isParametrized && !specialized(symbol)
        } foreach {
          case (symbol, loc) => self(symbol.decl, Map.empty, loc)
        }
      }

    }

    ////////////////////////////////////////////////////////////////////////////
    // Recursively specialize sub definitions and references
    ////////////////////////////////////////////////////////////////////////////

    val cursed = expanded flatMap { decl =>
      require(!decl.desc.isParametrized)

      var hadError = false

      val transform: TreeTransformer = new TreeTransformer {
        override val typed = false
        override val checkRefs = false

        def error(loc: Loc, msg: String*): Unit = {
          cc.error(loc, msg: _*)
          hadError = true
        }

        def error(tree: Tree, msg: String*): Unit = error(tree.loc, msg: _*)

        override def skip(tree: Tree): Boolean = tree match {
          // Skip parametrized definitions. These cannot be specialized without
          // parameter bindings and will be removed anyway. Also skip all
          // definitions which have already been specialized.
          case decl: Decl => decl.symbol.isParametrized || specialized(decl.symbol)
          // Skip parametrized references, these will now be specialized.
          // Also skip builtin symbols and already specialized symbols
          case ExprSym(symbol) => symbol.isParametrized || symbol.isBuiltin || specialized(symbol)
          //
          case _ => false
        }

        def typeCheck(tree: Tree*): Boolean =
          tree forall { cc.typeCheck(_) contains true } tap { hadError |= !_ }

        override def transform(tree: Tree): Tree = tree match {
          // Replace references if already specialized (e.g.: the typing
          // dependencies specialized above). We need this in order to be able
          // to call the type checker below for computing types
          case node @ ExprSym(symbol) =>
            cache.get(symbol) flatMap {
              _.get(Map.empty).flatten
            } map { decl =>
              ExprSym(decl.symbol) withLoc node.loc
            } getOrElse node

          // Leave the current definition alone
          case Decl(Sym(symbol, _), _) if symbol == decl.symbol => tree

          // Specialize nested definitions
          case decl: Decl if !decl.symbol.isParametrized && !specialized(decl.symbol) =>
            self(decl, Map.empty, tree.loc) getOrElse {
              hadError = true
              tree
            }

          // Transform calls to 'int'/'uint' to the corresponding sized TypeInt
          case ExprCall(ExprType(TypeNum(signed)), args) =>
            lazy val hint = if (signed) "int" else "uint"
            args match {
              case List(ArgP(expr)) =>
                if (!typeCheck(expr)) {
                  tree
                } else {
                  assert(expr.hasTpe)
                  expr.value match {
                    case None =>
                      error(expr, s"Width of '$hint' must be a compile time constant")
                      tree
                    case Some(v) if v < 1 =>
                      error(expr, s"Width of '$hint' must be positive, not $v")
                      tree
                    case Some(v) => ExprType(TypeInt(signed, v)) withLoc tree.loc
                  }
                }
              case _ =>
                error(tree, s"Bad parameter to '$hint', a single positional argument is expected.")
                tree
            }

          // Specialize types where used by the 'call' syntax
          case ExprCall(expr, args) if typeCheck(expr) =>
            expr.tpe match {
              case TypeType(_: TypeEntity) if args.isEmpty =>
                // This is to support legacy code where the empty parens were mandatory
                // in instantiations even if the entity wasn't parametrized.
                // TODO: Deprecate and remove?
                expr
              case TypeType(_) =>
                error(expr, "Type does not take any parameters")
                tree
              case TypeParametrized(symbol) =>
                val (posArgs, namedArgs) = args partition {
                  case _: ArgP => true
                  case _: ArgN => false
                }
                if (posArgs.nonEmpty) {
                  posArgs foreach { error(_, "Parameter assignments must be given by name") }
                  tree
                } else {
                  val bindings = Map from {
                    namedArgs.iterator collect { case ArgN(name, expr) => name -> expr }
                  }
                  self(symbol.decl, bindings, tree.loc) map { decl =>
                    ExprSym(decl.symbol) withLoc tree.loc
                  } getOrElse {
                    hadError = true
                    tree
                  }
                }
              case _ => tree
            }

          case _ => tree
        }
      }

      var result: Decl = decl

      result = (decl rewrite transform).asInstanceOf[Decl]

      if (hadError) None else Some(result)
    }

    cursed foreach dump("Cursed")

    ////////////////////////////////////////////////////////////////////////////
    // Replace all definitions and references with their specializations
    ////////////////////////////////////////////////////////////////////////////

    val replaced = cursed map { decl: Decl =>
      val transform: TreeTransformer = new TreeTransformer {
        override val typed = false
        override val checkRefs = false

        override def skip(tree: Tree): Boolean = tree match {
          case decl: Decl      => decl.symbol.isParametrized || specialized(decl.symbol)
          case ExprSym(symbol) => symbol.isBuiltin || specialized(symbol)
          case _               => false
        }

        def newDecls(symbol: Symbol, f: Decl => Tree, node: Tree): Tree =
          cache.get(symbol) match {
            case Some(map) =>
              val specializedDecls = List from {
                map.valuesIterator.flatten
              }
              Thicket(specializedDecls map {
                f(_) withLoc node.loc
              }) withLoc node.loc
            case None => node //Thicket(Nil) withLoc loc
          }

        override def transform(tree: Tree): Tree = tree match {
          // Replace references with specializations.
          case node @ ExprSym(symbol) =>
            cache.get(symbol) flatMap {
              _.get(Map.empty).flatten
            } map { decl =>
              ExprSym(decl.symbol) withLoc node.loc
            } getOrElse node

          // Replace definitions with their specialized versions
          case node: RizDecl  => newDecls(node.decl.symbol, RizDecl, node)
          case node: EntDecl  => newDecls(node.decl.symbol, EntDecl, node)
          case node: RecDecl  => newDecls(node.decl.symbol, RecDecl, node)
          case node: StmtDecl => newDecls(node.decl.symbol, StmtDecl, node)

          case _ => tree
        }
      }

      (decl rewrite transform).asInstanceOf[Decl]
    }

    replaced foreach dump("Replaced")

    val incomplete = replaced exists {
      _ exists {
        case _: Gen       => true
        case _: DescParam => true
      }
    }

    if (incomplete) {
      // TODO: Detect infinite recursion due to circular 'gen'
      specialize(replaced.get, unusedBindings, loc)
    } else {
      //////////////////////////////////////////////////////////////////////////
      // Everything expanded/specialized. Apply final transform.
      //////////////////////////////////////////////////////////////////////////

      unusedBindings foreach {
        case (name, _) =>
          cc.error(loc, s"'${decl.name}' has no parameter named '$name'")
      }

      val finalized = replaced flatMap { decl =>
        specialized add decl.symbol
        Finalize(decl) ensuring { _ forall { _.symbol eq decl.symbol } }
      }

      finalized foreach dump("Finalized")

      finalized
    }
  }

  private[this] def attempt(
      decl: Decl,
      paramBindings: Map[String, Expr],
      refLoc: Loc
  ): Option[Decl] = {
    //////////////////////////////////////////////////////////////////////////
    // Check for circular and divergent specialization
    //////////////////////////////////////////////////////////////////////////

    // TODO: detect divergence, currently it will just stack overflow

    val tag = (decl.symbol, paramBindings)

    pendingMap.get(tag) match {
      case Some(startLoc) =>
        // Already in progress. Report the cycle
        val color = AnsiColor.GREEN + AnsiColor.BOLD

        val msg = new ListBuffer[String]

        def bindingsNote(bindings: Map[String, Expr]): Unit = if (bindings.nonEmpty) {
          msg += bindings map {
            case (k, v) => s"$k = ${v.toSource}"
          } mkString ("with parameter assignments: ", ", ", "")
        }

        def sourceName(symbol: Symbol): String = symbol.attr.sourceName.get match {
          case Some((name, idxs)) =>
            assert(idxs.nonEmpty)
            idxs mkString (s"${name}#[", ", ", "]")
          case None => symbol.name
        }

        msg += s"Definition of '${sourceName(decl.symbol)}' is circular:"
        bindingsNote(paramBindings)
        msg += s"defined at ${decl.symbol.loc.prefix}"
        msg ++= decl.symbol.loc.context(color).split("\\s*\n") map { "  " + _ }

        def addEntry(
            symbol: Symbol,
            bindings: Map[String, Expr],
            loc: Loc,
            last: Boolean = false
        ): Unit = {
          msg += s"depends on '${sourceName(symbol)}' via ${loc.prefix}"
          bindingsNote(bindings)
          msg ++= loc.context(color).split("\\s*\n") map { "  " + _ }
          if (!last) {
            msg += s"defined at ${symbol.loc.prefix}"
            msg ++= symbol.loc.context(color).split("\\s*\n") map { "  " + _ }
          }
        }

        (pendingStack takeWhile { _ != tag }).reverse foreach {
          case t @ (symbol, bindings) => addEntry(symbol, bindings, pendingMap(t))
        }

        addEntry(decl.symbol, paramBindings, refLoc, last = true)

        cc.error(startLoc, msg.toList: _*)

        None

      case None =>
        // Good to go
        pendingMap(tag) = refLoc
        pendingStack push tag
        val result = specialize(decl, paramBindings, refLoc)
        pendingMap.remove(tag)
        pendingStack.pop

        // Quick sanity check: When we have finished with the root of the walk,
        // all symbols must have been specialized
        if (pendingStack.isEmpty && result.isDefined) {
          def check(tree: Tree): Unit = tree visit {
            case node @ Sym(symbol, _) if !specialized(symbol) =>
              cc.ice(node, "Unspecialized definition remains")
            case node @ ExprSym(symbol) if !specialized(symbol) && !symbol.isBuiltin =>
              cc.ice(node, "Unspecialized reference remains")
            case node: ExprRef =>
              cc.ice(node, "ExprRef remains")
            case node: DescChoice =>
              cc.ice(node, "DescChoice remains")
          }
          result foreach check
          specialized foreach { symbol =>
            check(symbol.decl)
          }
        }

        // Done
        result
    }
  }

  // Specialize definition given bindings for parameters
  def apply(
      decl: Decl,
      paramBindings: Map[String, Expr],
      refLoc: Loc
  ): Option[Decl] = {

    // If we have already performed this specialization, return that otherwise do it
    cache
      .getOrElseUpdate(decl.symbol, mutable.LinkedHashMap())
      .getOrElseUpdate(paramBindings, attempt(decl, paramBindings, refLoc))
  }

}
