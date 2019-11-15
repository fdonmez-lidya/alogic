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
// - Update Connects
// - Replace naked port references
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols._

final class LowerFlowControlB(implicit cc: CompilerContext) extends TreeTransformer {

  private[this] var inConnect = false

  override def enter(tree: Tree): Unit = tree match {
    case _: EntConnect => inConnect = true

    case _ => ()
  }

  // Given a symbol, return the corresponding payload symbol, if any
  private[this] def payloadSymbol(symbol: Symbol): Option[Symbol] = {
    symbol.attr.fcv.get.flatMap {
      _._1
    } orElse symbol.attr.fcr.get.flatMap {
      _._1
    } orElse symbol.attr.fca.get.flatMap {
      _._1
    }
  }

  // Given a symbol, return the corresponding valid symbol, if any
  private[this] def validSymbol(symbol: Symbol): Option[Symbol] = {
    symbol.attr.fcv.get.map {
      _._2
    } orElse symbol.attr.fcr.get.map {
      _._2
    } orElse symbol.attr.fca.get.map {
      _._2
    }
  }

  // Given a symbol, return the corresponding ready/accept symbol, if any
  private[this] def backSymbol(symbol: Symbol): Option[Symbol] = {
    symbol.attr.fcr.get.map {
      _._3
    } orElse symbol.attr.fca.get.map {
      _._3
    }
  }

  // Replace a reference/port expression with an equivalent expression
  // that refers to the constituent symbol extracted by partSymbol
  private[this] def partExpr(
      expr: Expr,
      partSymbol: Symbol => Option[Symbol]
  ): Option[Expr] = expr match {
    case ExprSym(pSymbol) => {
      partSymbol(pSymbol) map { symbol =>
        ExprSym(symbol)
      }
    }
    case ExprSelect(ExprSym(iSymbol), sel, _) if iSymbol.kind.isEntity => {
      val kind = iSymbol.kind.asEntity
      val pSymbolOpt = kind.publicSymbols collectFirst {
        case symbol if symbol.name == sel && symbol.attr.expandedPort.isSet => symbol
      }
      pSymbolOpt flatMap partSymbol map { symbol =>
        assert(kind(symbol.name).isDefined)
        ExprSelect(ExprSym(iSymbol), symbol.name, Nil)
      }
    }
    case _ => None
  }

  override def transform(tree: Tree): Tree = {
    val result: Tree = tree match {

      //////////////////////////////////////////////////////////////////////////
      // Expressions
      //////////////////////////////////////////////////////////////////////////

      case expr: ExprSym if !inConnect => {
        // Rewrite references to ports with fc as references to the payload
        partExpr(expr, payloadSymbol) getOrElse tree
      }

      //////////////////////////////////////////////////////////////////////////
      // Connect
      //////////////////////////////////////////////////////////////////////////

      case EntConnect(lhs, List(rhs)) => {
        // Expand inter-entity connections
        val pLhs = partExpr(lhs, payloadSymbol)
        val pRhs = partExpr(rhs, payloadSymbol)
        assert(pLhs.isDefined == pRhs.isDefined)

        val vLhs = partExpr(lhs, validSymbol)
        val vRhs = partExpr(rhs, validSymbol)
        assert(vLhs.isDefined == vRhs.isDefined)

        val bLhs = partExpr(lhs, backSymbol)
        val bRhs = partExpr(rhs, backSymbol)
        assert(bLhs.isDefined == bRhs.isDefined)

        val pConn = pLhs map { lhs =>
          EntConnect(lhs, pRhs.toList)
        }
        val vConn = vLhs map { lhs =>
          EntConnect(lhs, vRhs.toList)
        }
        val bConn = bRhs map { rhs =>
          EntConnect(rhs, bLhs.toList)
        }

        val newConns = List.concat(pConn, vConn, bConn)

        if (newConns.nonEmpty) Thicket(newConns) else tree
      } tap { _ =>
        inConnect = false
      }

      case _ => tree
    }

    // If we did modify the node, regularize it
    if (result ne tree) {
      result regularize tree.loc
    }

    // Done
    result
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(!inConnect)
  }

}

object LowerFlowControlB extends TreeTransformerPass {
  val name = "lower-flow-control-b"
  def create(implicit cc: CompilerContext) = new LowerFlowControlB
}
