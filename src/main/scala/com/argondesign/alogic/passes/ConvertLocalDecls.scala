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
// Remove StmtDecl instances:
//  - Lift StmtDecl to entity Decls
//  - Insert local initializer
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Types.Type
import com.argondesign.alogic.core.enums.UninitializedLocals
import com.argondesign.alogic.typer.TypeAssigner

import scala.collection.mutable.ListBuffer
import scala.util.Random

final class ConvertLocalDecls(implicit cc: CompilerContext) extends TreeTransformer {

  private[this] val localDecls = ListBuffer[Ent]()

  private[this] lazy val rng = new Random(entitySymbol.name.foldLeft(0)(_ ^ _))

  private[this] def getDefaultInitializer(kind: Type): Option[Expr] = {
    lazy val signed = kind.isSigned
    lazy val width = kind.width.toInt
    cc.settings.uninitialized match {
      case UninitializedLocals.None  => None
      case UninitializedLocals.Zeros => Some(ExprInt(signed, width, 0))
      case UninitializedLocals.Ones => {
        val expr = if (signed) {
          ExprInt(signed = true, width, -1)
        } else {
          ExprInt(signed = false, width, (BigInt(1) << width) - 1)
        }
        Some(expr)
      }
      case UninitializedLocals.Random => {
        val expr = (width, signed) match {
          case (1, true)  => ExprInt(signed = true, 1, -BigInt(1, rng))
          case (1, false) => ExprInt(signed = false, 1, BigInt(1, rng))
          case (n, true)  => ExprInt(signed = true, n, BigInt(n, rng) - (BigInt(1) << (n - 1)))
          case (n, false) => ExprInt(signed = false, n, BigInt(n, rng))
        }
        Some(expr)
      }
    }
  }

  override def skip(tree: Tree): Boolean = tree match {
    case _: Expr => true
    case _       => false
  }

  override def transform(tree: Tree): Tree = tree match {
    case StmtDecl(decl @ Decl(Sym(symbol, _), desc @ DescVar(_, initOpt))) =>
      localDecls.append(EntDecl(decl.copy(desc = desc.copy(initOpt = None))) regularize decl.loc)
      initOpt orElse getDefaultInitializer(symbol.kind) map { init =>
        StmtAssign(ExprSym(symbol), init) regularize tree.loc
      } getOrElse {
        Thicket(Nil) regularize tree.loc
      }

    case decl @ Decl(_, desc: DescEntity) if localDecls.nonEmpty =>
      val newBody = List.from(desc.body.iterator ++ localDecls.iterator)
      val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc tree.loc)
      TypeAssigner(decl.copy(desc = newDesc) withLoc tree.loc)

    case _ => tree
  }

  override protected def finalCheck(tree: Tree): Unit = {
    tree visit {
      case node: StmtDecl => cc.ice(node, "Local declaration remains")
    }
  }

}

object ConvertLocalDecls extends TreeTransformerPass {
  val name = "convert-local-decls"
  def create(implicit cc: CompilerContext) = new ConvertLocalDecls
}
