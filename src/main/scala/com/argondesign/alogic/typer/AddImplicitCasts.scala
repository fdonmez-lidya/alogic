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
// The Typer:
// - Type checks all tree nodes
// - Infers widths of unsized constants
// - Assigns types to all nodes using the TypeAssigner
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.typer

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.lib.Math.clog2
import com.argondesign.alogic.passes.TreeTransformerPass
import com.argondesign.alogic.util.FollowedBy

final class AddImplicitCasts(implicit cc: CompilerContext) extends TreeTransformer with FollowedBy {

  private def cast(kind: Type, expr: Expr) = {
    val castType = kind.underlying
    val castExpr = if (castType.isNum) expr.simplify else expr
    if (castType.isNum && !castExpr.isKnownConst) {
      cc.ice(expr, s"Trying to cast non-constant expression to type '${castType.toSource}'")
    }
    TypeAssigner(castExpr cast castType)
  }

  override def transform(tree: Tree): Tree = {
    val result = tree match {
      case decl @ Decl(symbol, Some(init))
          if (symbol.kind.isPacked && init.tpe.underlying.isNum) || (symbol.kind.underlying.isNum && init.tpe.isPacked) => {
        val newInit = cast(symbol.kind, init)
        if (symbol.kind.isConst) {
          symbol.attr.init set newInit
        }
        decl.copy(init = Some(newInit))
      }

      case stmt @ StmtAssign(lhs, rhs) if lhs.tpe.isPacked && rhs.tpe.underlying.isNum => {
        stmt.copy(rhs = cast(lhs.tpe, rhs))
      }

      case stmt @ StmtUpdate(lhs, _, rhs) if lhs.tpe.isPacked && rhs.tpe.underlying.isNum => {
        stmt.copy(rhs = cast(lhs.tpe, rhs))
      }

      // TODO: case ExprCall(expr, args) => tree

      case expr @ ExprIndex(tgt, idx) if idx.tpe.underlying.isNum => {
        val width = clog2(tgt.tpe.shapeIter.next) max 1
        val widthExpr = TypeAssigner(Expr(width) withLoc expr.loc)
        expr.copy(index = cast(TypeUInt(widthExpr), idx))
      }

      case expr @ ExprSlice(tgt, lidx, _, ridx)
          if lidx.tpe.underlying.isNum || ridx.tpe.underlying.isNum => {
        val width = clog2(tgt.tpe.shapeIter.next) max 1
        val widthExpr = TypeAssigner(Expr(width) withLoc expr.loc)
        val newLidx = if (lidx.tpe.isNum) cast(TypeUInt(widthExpr), lidx) else lidx
        val newRidx = if (ridx.tpe.isNum) cast(TypeUInt(widthExpr), ridx) else ridx
        expr.copy(lidx = newLidx, ridx = newRidx)
      }

      case expr @ ExprBinary(lhs,
                             "&" | "|" | "^" | "*" | "/" | "%" | "+" | "-" | ">" | ">=" | "<" |
                             "<=" | "==" | "!=",
                             rhs) if lhs.tpe.underlying.isNum != rhs.tpe.underlying.isNum => {
        if (lhs.tpe.isNum) {
          expr.copy(lhs = cast(rhs.tpe, lhs))
        } else {
          expr.copy(rhs = cast(lhs.tpe, rhs))
        }
      }

      case expr @ ExprTernary(_, tExpr, eExpr)
          if tExpr.tpe.underlying.isNum != eExpr.tpe.underlying.isNum => {
        if (tExpr.tpe.isNum) {
          expr.copy(thenExpr = cast(eExpr.tpe, tExpr))
        } else {
          expr.copy(elseExpr = cast(tExpr.tpe, eExpr))
        }
      }

      case _ => tree
    }

    if (result ne tree) TypeAssigner(result withLoc tree.loc) else tree
  }
}

object AddImplicitCasts extends TreeTransformerPass {
  val name = "add-implicit-casts"
  def create(implicit cc: CompilerContext) = new AddImplicitCasts
}