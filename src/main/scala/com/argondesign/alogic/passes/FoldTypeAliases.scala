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
// Remove all definitions with DescType
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.typer.TypeAssigner

final class FoldTypeAliases(implicit cc: CompilerContext) extends TreeTransformer {

  override def transform(tree: Tree): Tree = tree match {

    ////////////////////////////////////////////////////////////////////////////
    // Fold references to type symbols (unless it's directly to the named type)
    ////////////////////////////////////////////////////////////////////////////

    case expr @ ExprSym(symbol) if symbol.kind.isType =>
      val newExpr = symbol.kind.asType.kind match {
        case kind: TypeInt           => ExprType(kind)
        case kind: TypeNum           => ExprType(kind)
        case kind: TypeVector        => ExprType(kind)
        case TypeVoid                => ExprType(TypeVoid)
        case TypeStr                 => ExprType(TypeStr)
        case TypeEntity(`symbol`, _) => expr
        case TypeRecord(`symbol`, _) => expr
        case TypeEntity(s, _)        => ExprSym(s)
        case TypeRecord(s, _)        => ExprSym(s)
      }
      newExpr regularize tree.loc

    ////////////////////////////////////////////////////////////////////////////
    // Drop DescType definitions
    ////////////////////////////////////////////////////////////////////////////

    case RizDecl(Decl(_, _: DescType))  => TypeAssigner(Thicket(Nil) withLoc tree.loc)
    case EntDecl(Decl(_, _: DescType))  => TypeAssigner(Thicket(Nil) withLoc tree.loc)
    case RecDecl(Decl(_, _: DescType))  => TypeAssigner(Thicket(Nil) withLoc tree.loc)
    case StmtDecl(Decl(_, _: DescType)) => TypeAssigner(Thicket(Nil) withLoc tree.loc)

    ////////////////////////////////////////////////////////////////////////////
    // Otherwise
    ////////////////////////////////////////////////////////////////////////////

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    // Should have removed all StmtLet, StmtUpdate, StmtPost
    tree visit {
      case node @ Decl(_, _: DescType) => cc.ice(node, s"DescType remains")
    }
  }

}

object FoldTypeAliases extends TreeTransformerPass {
  val name = "fold-type-aliases"
  def create(implicit cc: CompilerContext) = new FoldTypeAliases

  override def apply(trees: List[Tree])(implicit cc: CompilerContext): List[Tree] = super.apply {
    trees filter {
      case Decl(_, _: DescType) => false
      case _                    => true
    }
  }
}
