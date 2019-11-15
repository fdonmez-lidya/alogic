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
//   - Update instance ports selects
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._

import scala.collection.mutable

final class SplitStructsB(implicit cc: CompilerContext) extends TreeTransformer {

  private[this] val fieldIndexStack = mutable.Stack[Int]()

  override def enter(tree: Tree) = tree match {
    case ExprSelect(expr, sel, _) =>
      expr.tpe.underlying match {
        case kind: TypeRecord => fieldIndexStack push kind.publicSymbols.indexWhere(_.name == sel)
        case _                => fieldIndexStack push -1
      }

    case _ => ()
  }

  override def transform(tree: Tree): Tree = tree match {
    case ExprSelect(ExprSym(iSymbol), sel, _) if iSymbol.kind.isEntity => {
      // Rewrite selects of form instance.port
      val kind = iSymbol.kind.asEntity
      val pSymbol = kind(sel).get
      pSymbol.attr.fieldSymbols.get map { fSymbols =>
        def cat(struct: TypeRecord)(implicit it: Iterator[Symbol]): ExprCat = ExprCat {
          for (symbol <- struct.publicSymbols) yield {
            symbol.kind match {
              case struct: TypeRecord => cat(struct)
              case _                  => ExprSelect(ExprSym(iSymbol), it.next().name, Nil)
            }
          }
        }
        cat(pSymbol.kind.underlying.asRecord)(fSymbols.iterator) regularize tree.loc
      } getOrElse {
        tree
      }
    } tap { _ =>
      fieldIndexStack.pop()
    }

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

    case _ => tree
  }

}

object SplitStructsB extends TreeTransformerPass {
  val name = "split-structs-b"
  def create(implicit cc: CompilerContext) = new SplitStructsB
}
