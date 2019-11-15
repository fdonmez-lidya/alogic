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
// Replace external port references to dict ports with a reference to the
// expanded port
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext

final class ResolveDictSel(implicit cc: CompilerContext) extends TreeTransformer {

  override val typed: Boolean = false

  def values(idxs: List[Expr])(implicit cc: CompilerContext): Option[List[BigInt]] = idxs match {
    case Nil => Some(Nil)
    case head :: tail =>
      val resOpt = values(tail) // Compute eagerly to emit all errors
      head.value match {
        case Some(value) => resOpt map { value :: _ }
        case None        => cc.error(head, "Identifier index must be a compile time constant"); None
      }
  }

  override def transform(tree: Tree): Tree = tree match {
    // Error for referencing x.p#[n] as x.p__n
    case ExprSelect(ExprSym(iSymbol), sel, Nil) if iSymbol.kind.isEntity =>
      iSymbol.kind.asEntity.publicSymbols exists { pSymbol =>
        !pSymbol.attr.sourceName.isSet && pSymbol.name == sel
      } pipe {
        case true => tree
        case false =>
          cc.error(tree, s"No port named '$sel' on instance '${iSymbol.name}'")
          ExprError() withLoc tree.loc
      }

    case ExprSelect(expr, sel, idxs) if idxs.nonEmpty =>
      val res = expr match {
        case ExprSym(iSymbol) if iSymbol.kind.isEntity =>
          values(idxs) map { idxValues =>
            iSymbol.kind.asEntity.publicSymbols collectFirst {
              case portSymbol if portSymbol.attr.sourceName.contains((sel, idxValues)) =>
                ExprSelect(expr, portSymbol.name, Nil)
            } getOrElse {
              val srcName = idxValues.mkString(sel + "#[", ", ", "]")
              cc.error(tree, s"No port named '$srcName' on instance '${iSymbol.name}'")
              ExprError()
            }
          } getOrElse {
            ExprError()
          }
        case _ =>
          cc.error(tree, "Illegal use of '.' lookup with dictionary indices")
          ExprError()
      }
      res withLoc tree.loc

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    tree visitAll {
      case node @ ExprSelect(_, _, idxs) if idxs.nonEmpty =>
        cc.ice(node, s"ExprSelect with indices remains")
    }
  }
}

object ResolveDictSel extends TreeTransformerPass {
  val name = "resolve-dict-ports"
  def create(implicit cc: CompilerContext) = new ResolveDictSel
}
