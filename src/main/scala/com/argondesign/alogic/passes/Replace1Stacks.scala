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
// Replace stacks of depth 1 without accesses to empty/full with local flops
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols._

import scala.collection.mutable

final class Replace1Stacks(implicit cc: CompilerContext) extends TreeTransformer {

  // Map from original stack variable symbol to the corresponding replacement,
  private[this] val stackMap = mutable.LinkedHashMap[Symbol, Symbol]()

  override def skip(tree: Tree): Boolean = tree match {
    case Decl(_, desc: DescEntity) => desc.decls.isEmpty
    case Decl(_, _: DescRecord)    => true
    case _                         => false
  }

  override def enter(tree: Tree): Unit = tree match {
    // TODO: iff no access to empty/full ports
    case Decl(Sym(symbol, _), DescStack(_, depth)) if depth.value contains BigInt(1) =>
      stackMap(symbol) = cc.newSymbolLike(symbol) tap { _.kind = symbol.kind.asStack.kind }

    case _ =>
  }

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // Replace the stack decl with the decl of the new symbol
      //////////////////////////////////////////////////////////////////////////

      case Decl(Sym(s, _), _: DescStack) => stackMap(s).decl

      //////////////////////////////////////////////////////////////////////////
      // Rewrite statements
      //////////////////////////////////////////////////////////////////////////

      case StmtExpr(ExprCall(ExprSelect(ExprSym(s), "push" | "set", _), List(ArgP(arg)))) =>
        stackMap.get(s) map { symbol =>
          StmtAssign(ExprSym(symbol), arg)
        } getOrElse tree

      //////////////////////////////////////////////////////////////////////////
      // Rewrite expressions
      //////////////////////////////////////////////////////////////////////////

      case ExprCall(ExprSelect(ExprSym(s), "pop" | "top", _), Nil) =>
        stackMap.get(s) map { symbol =>
          ExprSym(symbol)
        } getOrElse tree

      case ExprSelect(ExprSym(s), "full" | "empty", _) if stackMap contains s =>
        cc.ice(tree, "Replacing 1 deep stack with full access")

      case _ => tree
    }

    // If we did modify the node, regularize it
    if (result ne tree) {
      result regularize tree.loc
    }

    // Done
    result
  }

}

object Replace1Stacks extends TreeTransformerPass {
  val name = "replace-1-stacks"
  def create(implicit cc: CompilerContext) = new Replace1Stacks
}
