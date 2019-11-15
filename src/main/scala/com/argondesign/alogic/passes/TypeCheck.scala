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

import com.argondesign.alogic.ast.Trees.Tree
import com.argondesign.alogic.core.CompilerContext

object TypeCheck extends Pass {
  val name = "type-check"

  def apply(trees: List[Tree])(implicit cc: CompilerContext): List[Tree] = {
    trees filter { cc.typeCheck(_) contains true }
  }
}
