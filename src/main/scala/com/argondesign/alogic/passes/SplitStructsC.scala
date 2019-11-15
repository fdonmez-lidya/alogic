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
//   - Remove struct ports
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.typer.TypeAssigner

final class SplitStructsC(implicit cc: CompilerContext) extends TreeTransformer {

  override def transform(tree: Tree): Tree = tree match {
    // Types for entities changed. Re-type references
    case expr @ ExprSym(symbol) if symbol.kind.isEntity || symbol.kind.isType =>
      TypeAssigner(expr.copy() withLoc expr.loc)

    case desc: DescEntity =>
      // Drop original port declarations
      val newBody = desc.body filterNot {
        case EntDecl(decl) => decl.symbol.attr.fieldSymbols.isSet
        case _             => false
      }
      TypeAssigner(desc.copy(body = newBody) withLoc tree.loc)

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    tree visit {
      case node @ Decl(_, _: DescRecord) =>
        cc.ice(node, "Struct declaration remains")
      case node: Tree if node.tpe.underlying.isRecord =>
        cc.ice(node, "Tree of type struct remains", node.toString)
    }
  }

}

object SplitStructsC extends TreeTransformerPass {
  val name = "split-structs-c"
  def create(implicit cc: CompilerContext) = new SplitStructsC
}
