////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018-2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Desugar rewrites basic syntactic sugar into their equivalent form.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

final class Desugar(implicit cc: CompilerContext) extends TreeTransformer {

  override def transform(tree: Tree): Tree = tree match {
    // "a++" rewritten as  "a = a + <width of a>'d1"
    case StmtPost(lhs, op) =>
      val one = TypeAssigner(ExprInt(false, lhs.tpe.width.toInt, 1) withLoc tree.loc)
      val rhs = op match {
        case "++" => lhs + one
        case "--" => lhs - one
        case _    => unreachable
      }
      TypeAssigner(StmtAssign(lhs, rhs) withLoc tree.loc)

    // "a += b" rewritten as "a = a + b"
    case StmtUpdate(lhs, op, expr) =>
      StmtAssign(lhs, ExprBinary(lhs, op, expr)) regularize tree.loc

    // "let(<init>) <stmts>" rewritten as "<init> <stmts>"
    case StmtLet(inits, stmts) => TypeAssigner(Thicket(inits ::: stmts) withLoc tree.loc)

    // "new entity <name> {<body>}" rewritten as "entity <name> {<body>} <name> = new <name>();"
    case ent @ EntDecl(Decl(_, DescSingleton(variant, body))) =>
      val descEntity = TypeAssigner(DescEntity(variant, body) withLoc ent.decl.desc.loc)
      val eSymbol = ent.decl.symbol.dup
      val symEntity = TypeAssigner(Sym(eSymbol, Nil) withLoc ent.decl.ref.loc)
      val declEntity = TypeAssigner(Decl(symEntity, descEntity) withLoc ent.decl.loc)
      val entEntity = TypeAssigner(EntDecl(declEntity) withLoc ent.loc)

      val specInstance = TypeAssigner(ExprSym(eSymbol) withLoc ent.decl.ref.loc)
      val descInstance = TypeAssigner(DescInstance(specInstance) withLoc ent.decl.desc.loc)
      val declInstance = TypeAssigner(ent.decl.copy(desc = descInstance) withLoc ent.decl.loc)
      val entInstance = TypeAssigner(EntDecl(declInstance) withLoc ent.loc)

      TypeAssigner(Thicket(List(entEntity, entInstance)) withLoc tree.loc)

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    // Should have removed all StmtLet, StmtUpdate, StmtPost
    tree visit {
      case node: StmtLet    => cc.ice(node, s"StmtLet remains")
      case node: StmtUpdate => cc.ice(node, s"StmtUpdate remains")
      case node: StmtPost   => cc.ice(node, s"StmtPost remains")
    }
  }

}

object Desugar extends TreeTransformerPass {
  val name = "desugar"
  def create(implicit cc: CompilerContext) = new Desugar
}
