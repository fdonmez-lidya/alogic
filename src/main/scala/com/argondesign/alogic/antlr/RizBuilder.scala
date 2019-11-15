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
// Build a Rec AST from an Antlr4 parse tree
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.antlr

import com.argondesign.alogic.antlr.AlogicParser._
import com.argondesign.alogic.antlr.AntlrConverters._
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FuncVariant

object RizBuilder extends BaseBuilder[RizContext, Riz] {
  def apply(ctx: RizContext)(implicit cc: CompilerContext): Riz = {
    object Visitor extends AlogicScalarVisitor[Riz] {
      override def visitRizDecl(ctx: RizDeclContext): Riz = {
        val decl = DeclBuilder(ctx.decl) match {
          case func @ Decl(_, desc: DescFunc) =>
            func.copy(desc = desc.copy(variant = FuncVariant.Comb) withLoc desc.loc) withLoc func.loc
          case other => other
        }
        RizDecl(decl) withLoc ctx.loc
      }
    }

    Visitor(ctx)
  }
}
