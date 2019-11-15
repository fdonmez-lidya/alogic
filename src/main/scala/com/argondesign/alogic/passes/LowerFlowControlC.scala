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
// Do:
// - Remove expanded ports
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeNone
import com.argondesign.alogic.core.StorageTypes.StorageTypeSlices
import com.argondesign.alogic.typer.TypeAssigner

final class LowerFlowControlC(implicit cc: CompilerContext) extends TreeTransformer {

  override def skip(tree: Tree): Boolean = tree match {
    case _: Expr => true
    case _       => false
  }

  override def transform(tree: Tree): Tree = tree match {
    // Drop original port declarations
    case EntDecl(Decl(Sym(symbol, _), _)) if symbol.attr.expandedPort.isSet =>
      TypeAssigner(Thicket(Nil) withLoc tree.loc)

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    tree visit {
      case node @ DescOut(_, fc, _, _) if fc != FlowControlTypeNone =>
        cc.ice(node, "Port with flow control remains")
      case node @ DescOut(_, _, _: StorageTypeSlices, _) =>
        cc.ice(node, "Port with output slices remains")
    }
  }

}

object LowerFlowControlC extends TreeTransformerPass {
  val name = "lower-flow-control-c"
  def create(implicit cc: CompilerContext) = new LowerFlowControlC
}
