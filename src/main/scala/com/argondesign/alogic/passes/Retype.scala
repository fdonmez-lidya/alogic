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
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.typer.TypeAssigner

final class Retype(implicit cc: CompilerContext) extends TreeTransformer {

  // skip unary tick as it's type is not computable locally
  override def skip(tree: Tree): Boolean = tree match {
    case ExprUnary("'", _) => true
    case _                 => false
  }

  // Re-type references
  override def transform(tree: Tree): Tree = tree match {
    case expr: ExprSym => TypeAssigner(expr.copy() withLoc expr.loc)
    case _             => tree
  }
}

object Retype extends TreeTransformerPass {
  val name = "retype"
  def create(implicit cc: CompilerContext) = new Retype
}
