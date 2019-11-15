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
// - Lower stack variables into stack instances
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.StackFactory
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types.TypeStack
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

final class LowerStacks(implicit cc: CompilerContext) extends TreeTransformer {

  // Map from original stack variable symbol to the
  // corresponding stack entity and instance symbols
  private[this] val stackMap = mutable.Map[Symbol, (Decl, Symbol)]()

  // Stack of extra statements to emit when finished with a statement
  private[this] val extraStmts = mutable.Stack[mutable.ListBuffer[Stmt]]()

  override def skip(tree: Tree): Boolean = tree match {
    case Decl(_, DescEntity(EntityVariant.Net, _)) => true
    case _                                         => false
  }

  override def enter(tree: Tree): Unit = tree match {
    case Decl(Sym(symbol, _), _: DescStack) =>
      symbol.kind match {
        case TypeStack(kind, depth) =>
          // Construct the stack entity
          val loc = tree.loc
          val pName = symbol.name
          // TODO: mark inline
          val eName = entitySymbol.name + cc.sep + "stack" + cc.sep + pName
          val stackEntity = StackFactory(eName, loc, kind, depth)
          val instanceSymbol = cc.newSymbol(pName, loc) tap {
            _.kind = stackEntity.symbol.kind.asType.kind
          }
          stackMap(symbol) = (stackEntity, instanceSymbol)
          // Clear enable when the entity stalls
          entitySymbol.attr.interconnectClearOnStall.append((instanceSymbol, "en"))
        case _ => unreachable
      }

    case _: Stmt =>
      // Whenever we enter a new statement, add a new buffer to
      // store potential extra statements
      extraStmts.push(ListBuffer())

    case _ =>
  }

  private[this] def assignTrue(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 1))
  private[this] def assignFalse(expr: Expr) = StmtAssign(expr, ExprInt(false, 1, 0))

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // Rewrite statements
      //////////////////////////////////////////////////////////////////////////

      case StmtExpr(ExprCall(ExprSelect(ExprSym(symbol), "push", _), List(ArgP(arg)))) => {
        stackMap.get(symbol) map {
          case (_, iSymbol) => {
            StmtBlock(
              List(
                assignTrue(ExprSym(iSymbol) select "en"),
                assignTrue(ExprSym(iSymbol) select "push"),
                StmtAssign(ExprSym(iSymbol) select "d", arg)
              ))
          }
        } getOrElse {
          tree
        }
      }

      case StmtExpr(ExprCall(ExprSelect(ExprSym(symbol), "set", _), List(ArgP(arg)))) => {
        stackMap.get(symbol) map {
          case (_, iSymbol) => {
            StmtBlock(
              List(
                assignTrue(ExprSym(iSymbol) select "en"),
                StmtAssign(ExprSym(iSymbol) select "d", arg)
              ))
          }
        } getOrElse {
          tree
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Rewrite expressions
      //////////////////////////////////////////////////////////////////////////

      case ExprCall(ExprSelect(ExprSym(symbol), "pop", _), Nil) => {
        stackMap.get(symbol) map {
          case (_, iSymbol) => {
            extraStmts.top append assignTrue(ExprSym(iSymbol) select "en")
            extraStmts.top append assignTrue(ExprSym(iSymbol) select "pop")
            ExprSym(iSymbol) select "q"
          }
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "top", _) => {
        stackMap.get(symbol) map {
          case (_, iSymbol) => ExprSym(iSymbol) select "q"
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "full", _) => {
        stackMap.get(symbol) map {
          case (_, iSymbol) => ExprSym(iSymbol) select "full"
        } getOrElse {
          tree
        }
      }

      case ExprSelect(ExprSym(symbol), "empty", _) => {
        stackMap.get(symbol) map {
          case (_, iSymbol) => ExprSym(iSymbol) select "empty"
        } getOrElse {
          tree
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Add stack entities
      //////////////////////////////////////////////////////////////////////////

      case decl @ Decl(_, desc: DescEntity) if stackMap.nonEmpty => {
        val newBody = List from {
          // Drop stack declarations and the comb process
          desc.body.iterator filter {
            case EntDecl(Decl(_, _: DescStack)) => false
            case _: EntCombProcess              => false
            case _                              => true
          } concat {
            // Add instances
            stackMap.valuesIterator map { case (_, iSymbol) => iSymbol.decl } map EntDecl
          } concat {
            Iterator single {
              // Add leading statements to the state system
              assert(desc.combProcesses.lengthIs <= 1)

              val leading = stackMap.values map {
                _._2
              } map { iSymbol =>
                val iRef = ExprSym(iSymbol)
                StmtBlock(
                  List(
                    assignFalse(iRef select "en"),
                    StmtAssign(iRef select "d", iRef select "q"), // TODO: redundant
                    assignFalse(iRef select "push"), // TODO: redundant
                    assignFalse(iRef select "pop") // TODO: redundant
                  )
                )
              }

              desc.combProcesses.headOption map {
                case EntCombProcess(stmts) => EntCombProcess(List.concat(leading, stmts))
              } getOrElse {
                EntCombProcess(leading.toList)
              }
            }
          }
        }

        val newDecl = decl.copy(desc = desc.copy(body = newBody))
        val stackEntities = stackMap.values map { _._1 }
        Thicket(newDecl :: stackEntities.toList)
      }

      case _ => tree
    }

    // Emit any extra statement with this statement
    val result2 = result match {
      case stmt: Stmt =>
        val extra = extraStmts.pop()
        if (extra.isEmpty) stmt else StmtBlock((extra append stmt).toList)
      case _ => result
    }

    // If we did modify the node, regularize it
    if (result2 ne tree) {
      result2 regularize tree.loc
    }

    // Done
    result2
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(extraStmts.isEmpty)

    tree visit {
      case node @ ExprSelect(ref, sel, _) if ref.tpe.isStack => cc.ice(node, s"Stack .$sel remains")
    }
  }

}

object LowerStacks extends TreeTransformerPass {
  val name = "lower-stacks"
  def create(implicit cc: CompilerContext) = new LowerStacks
}
