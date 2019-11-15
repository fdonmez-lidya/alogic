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
// Remove local variable and port symbols which are never used
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.analysis.ReadSymbols
import com.argondesign.alogic.analysis.WrittenSymbols
import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees.Expr.InstancePortRef
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.immutable.HashSet
import scala.collection.mutable

final class RemoveUnused(unusedSymbols: Set[Symbol])(implicit cc: CompilerContext)
    extends TreeTransformer {

  private[this] val ourUnused = mutable.HashSet[Symbol]()

  override def enter(tree: Tree): Unit = tree match {
    case desc: DescEntity =>
      for (Decl(Sym(symbol, _), _) <- desc.decls if unusedSymbols contains symbol) {
        ourUnused add symbol
      }

    case _ => ()
  }

  def emptyStmt(stmt: Stmt): Boolean = stmt match {
    case StmtBlock(body)         => body forall emptyStmt
    case StmtIf(_, eBody, tBody) => (eBody forall emptyStmt) && (tBody forall emptyStmt)
    case StmtCase(_, cases) =>
      cases forall {
        case CaseRegular(_, stmts) => stmts forall emptyStmt
        case CaseDefault(stmts)    => stmts forall emptyStmt
        case _: CaseGen            => unreachable
      }
    case _ => false
  }

  override def transform(tree: Tree): Tree = tree match {

    ////////////////////////////////////////////////////////////////////////////
    // Fold empty statements
    ////////////////////////////////////////////////////////////////////////////

    case stmt: Stmt if emptyStmt(stmt) => TypeAssigner(Thicket(Nil) withLoc tree.loc)

    ////////////////////////////////////////////////////////////////////////////
    // Remove assignments that write only unused symbols
    ////////////////////////////////////////////////////////////////////////////

    case StmtAssign(lhs, _) if WrittenSymbols(lhs) forall ourUnused.contains =>
      TypeAssigner(Thicket(Nil) withLoc tree.loc)

    ////////////////////////////////////////////////////////////////////////////
    // Remove declarations and connections to unused symbols
    ////////////////////////////////////////////////////////////////////////////

    case desc: DescEntity =>
      // If we are removing a _q, drop the suffix from the _d
      for {
        qSymbol <- ourUnused
        dSymbol <- qSymbol.attr.flop.get
      } {
        assert(dSymbol.name endsWith "_d")
        dSymbol.name = dSymbol.name.dropRight(2)
        dSymbol.attr.combSignal set true
      }

      // Remove:
      // - declarations of unused symbols
      // - connects driving only unused symbols
      val newBody = desc.body filterNot {
        case EntDecl(decl) => ourUnused contains decl.symbol
        case EntConnect(_, List(InstancePortRef(iSymbol, pSymbol))) =>
          unusedSymbols.contains(iSymbol) || unusedSymbols.contains(pSymbol)
        case EntConnect(_, List(rhs)) => WrittenSymbols(rhs) forall ourUnused.contains
        case _                        => false
      }

      TypeAssigner(desc.copy(body = newBody) withLoc tree.loc)

    case _ => tree
  }

}

object RemoveUnused extends Pass {
  val name = "remove-unused"

  private def gather(entities: List[Decl])(f: Decl => Iterator[Symbol]): Set[Symbol] =
    HashSet from { entities flatMap f }

  @tailrec
  private def loop(entities: List[Decl])(implicit cc: CompilerContext): List[Decl] = {

    // TODO: Could prune every entity completely that has only inputs left

    // TODO: Rename interconnect for removed ports

    // Gather all symbols considered for removal
    val candidateSymbols = gather(entities) { entity =>
      val eSymbol = entity.symbol
      val desc = entity.desc.asInstanceOf[DescEntity]

      val isTopLevel = eSymbol.attr.topLevel.get contains true

      val eSymbols = if (isTopLevel) Iterator.empty else Iterator.single(eSymbol)

      val dSymbols = if (desc.variant == EntityVariant.Ver) {
        // Retain all definitions for verbatim entities
        Iterator.empty
      } else {
        val stateVarQ = eSymbol.attr.stateVar.get
        val stateVarD = stateVarQ map { _.attr.flop.value }
        desc.decls.iterator filter {
          case Decl(_, _: DescInstance) => false
          case _                        => true
        } map {
          _.symbol
        } filterNot { symbol =>
          // Retain the state variables if they exist
          (stateVarQ contains symbol) || (stateVarD contains symbol)
        } filter { // Retain inputs and outputs of top level entities
          _.kind match {
            case _: TypeIn  => !isTopLevel
            case _: TypeOut => !isTopLevel
            case _          => true
          }
        }
      }

      val iSymbols = desc.instances.iterator map { _.symbol }

      // TODO: simplify by unifying dSymbols and iSymbols
      eSymbols ++ dSymbols ++ iSymbols
    }

    // Gather all used symbols. A symbol is used if it's value is consumed,
    // this can happen when it is read in an rvalue, read in an lvalue, or
    // is instantiated. Furthermore all flop _d signals and array
    // _we/_waddr/_wdata signals are used. At the moment we also cannot remove
    // symbols that are written through a concatenation lvalue, as they are
    // required as placeholders
    val usedSymbols = gather(entities) {
      _ flatCollect {
        case Decl(_, DescInstance(ExprSym(eSymbol))) => Iterator.single(eSymbol)
        case EntConnect(lhs, List(rhs: ExprCat)) => {
          // Concatenation on the right, everything is used, if only as a placeholder
          // TODO: if any symbol in the concatenation is used, then all are used
          val lSymbols = lhs match {
            case InstancePortRef(iSymbol, pSymbol) => Iterator(iSymbol, pSymbol)
            case _                                 => ReadSymbols.rval(lhs)
          }
          val rSymbols = rhs collect { case ExprSym(symbol) => symbol }
          lSymbols ++ rSymbols
        }
        case EntConnect(InstancePortRef(iSymbol, pSymbol), List(rhs)) => {
          // instance.port on left hand side
          Iterator(iSymbol, pSymbol) ++ ReadSymbols.lval(rhs)
        }
        case EntConnect(lhs, List(InstancePortRef(_, _))) => {
          // instance.port on right hand side
          ReadSymbols.rval(lhs)
        }
        case EntConnect(lhs, List(rhs)) => {
          // Everything on the left, but on the right only stuff that is read
          ReadSymbols.rval(lhs) ++ ReadSymbols.lval(rhs)
        }
        case stmt @ StmtAssign(_: ExprCat, _) => {
          // Concatenation on the left, everything is used, if only as a placeholder
          // TODO: if any symbol in the concatenation is used, then all are used
          stmt collect { case ExprSym(symbol) => symbol }
        }
        case StmtAssign(lhs, rhs) => {
          // Everything on the right, but on the left only stuff that is read
          ReadSymbols.lval(lhs) ++ ReadSymbols.rval(rhs)
        }
        case Decl(Sym(symbol, _), _) if symbol.attr.flop.isSet => {
          // Flop _d
          symbol.attr.flop.get.iterator
        }
        case Decl(Sym(symbol, _), _) if symbol.attr.memory.isSet => {
          // Array _we/_waddr/_wdata
          val (we, waddr, wdata) = symbol.attr.memory.value
          Iterator(we, waddr, wdata)
        }
        case ExprSym(symbol) => {
          // Any other reference is used
          Iterator.single(symbol)
        }
      }
    }

    // Compute the unused ports
    val unusedSymbols = candidateSymbols diff usedSymbols

    if (unusedSymbols.isEmpty) {
      entities
    } else {
      // Remove unused entities
      val usedEntities = entities filterNot { unusedSymbols contains _.symbol }

      // Remove symbols
      val results = List from {
        usedEntities map { entity =>
          (new RemoveUnused(unusedSymbols)(cc))(entity).asInstanceOf[Decl]
        }
      }

      // Iterate until we no longer have any unused ports
      loop(results)
    }
  }

  def apply(trees: List[Tree])(implicit cc: CompilerContext): List[Tree] = {
    val entities = trees map {
      case entity @ Decl(_, _: DescEntity) => entity
      case _                               => unreachable
    }
    loop(entities)
  }
}
