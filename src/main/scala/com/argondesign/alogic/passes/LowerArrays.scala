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
// Lower arrays into constituent signals
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.lib.Math
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

final class LowerArrays(implicit cc: CompilerContext) extends TreeTransformer {

  override def skip(tree: Tree): Boolean = tree match {
    case Decl(_, desc: DescEntity) => desc.combProcesses.isEmpty
    case _                         => false
  }

  override def enter(tree: Tree): Unit = tree match {

    case Decl(Sym(symbol, _), _: DescArray) =>
      symbol.kind match {
        case TypeArray(kind, size) =>
          val loc = tree.loc
          val name = symbol.name
          // Append _q to array name symbol
          symbol.name = s"${name}_q"
          // Create we symbol
          val weSymbol = cc.newSymbol(s"${name}_we", loc) tap { _.kind = TypeUInt(1) }
          // Create waddr symbol
          val abits = Math.clog2(size) ensuring { _ > 0 }
          val waSymbol = cc.newSymbol(s"${name}_waddr", loc) tap { _.kind = TypeUInt(abits) }
          // Create wdata symbol
          val dbits = kind.width
          val wdSymbol = cc.newSymbol(s"${name}_wdata", loc) tap { _.kind = TypeUInt(dbits) }
          // Set attributes
          symbol.attr.memory.set((weSymbol, waSymbol, wdSymbol))
        case _ => unreachable
      }

    case _ =>
  }

  override def transform(tree: Tree): Tree = tree match {

    //////////////////////////////////////////////////////////////////////////
    // Rewrite .write calls
    //////////////////////////////////////////////////////////////////////////

    case StmtExpr(
        ExprCall(ExprSelect(ExprSym(symbol), "write", _), List(ArgP(addr), ArgP(data)))) =>
      // Rewrite assignments to array elements
      symbol.attr.memory.get map {
        case (weSymbol, waSymbol, wdSymbol) =>
          Thicket(
            List(
              StmtAssign(ExprSym(weSymbol), ExprInt(false, 1, 1)),
              StmtAssign(ExprSym(waSymbol), addr),
              StmtAssign(ExprSym(wdSymbol), data)
            )) regularize tree.loc
      } getOrElse {
        tree
      }

    //////////////////////////////////////////////////////////////////////////
    // Add declarations
    //////////////////////////////////////////////////////////////////////////

    case decl @ EntDecl(Decl(Sym(symbol, _), _)) =>
      symbol.attr.memory.get map {
        case (weSymbol, waSymbol, wdSymbol) =>
          Thicket(
            List(
              decl,
              EntDecl(weSymbol.decl),
              EntDecl(waSymbol.decl),
              EntDecl(wdSymbol.decl)
            )) regularize tree.loc
      } getOrElse {
        tree
      }

    //////////////////////////////////////////////////////////////////////////
    // Add _we/_waddr/_wdata = 'b0 fence statements
    //////////////////////////////////////////////////////////////////////////

    case desc: DescEntity =>
      assert(desc.combProcesses.lengthIs == 1)

      val newBody = desc.body map {
        // Add assignments
        case ent @ EntCombProcess(stmts) =>
          val leading = desc.decls collect {
            case decl @ Decl(Sym(symbol, _), _: DescArray) =>
              val (weSymbol, waSymbol, wdSymbol) = symbol.attr.memory.value
              StmtBlock(
                List(
                  StmtAssign(ExprSym(weSymbol), ExprInt(false, 1, 0)),
                  StmtAssign(ExprSym(waSymbol), ExprInt(false, waSymbol.kind.width.toInt, 0)),
                  StmtAssign(ExprSym(wdSymbol), ExprInt(false, wdSymbol.kind.width.toInt, 0))
                )
              ) regularize decl.loc
          }
          TypeAssigner(EntCombProcess(leading ::: stmts) withLoc ent.loc)
        case other => other
      }

      TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)

    case _ => tree
  }

}

object LowerArrays extends TreeTransformerPass {
  val name = "lower-arrays"
  def create(implicit cc: CompilerContext) = new LowerArrays
}
