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
// Convert register output ports to local register connected to wire output port
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.enums.EntityVariant

final class LowerRegPorts(implicit cc: CompilerContext) extends TreeTransformer {

  override def skip(tree: Tree): Boolean = tree match {
    case Decl(_, DescEntity(EntityVariant.Net, _)) => true
    case Decl(_, _: DescRecord)                    => true
    case _                                         => false
  }

  override def enter(tree: Tree): Unit = tree match {
    case Decl(Sym(symbol, _), DescOut(_, _, StorageTypeReg, _)) =>
      // Allocate local register
      val rName = "oreg" + cc.sep + symbol.name
      val rSymbol = cc.newSymbol(rName, tree.loc) tap { _.kind = symbol.kind.underlying }
      // Move the clearOnStall attribute to the register symbol
      symbol.attr.clearOnStall.get foreach { attr =>
        rSymbol.attr.clearOnStall set attr
        symbol.attr.clearOnStall.clear()
      }
      // Move the default attribute to the register symbol
      symbol.attr.default.get foreach { attr =>
        rSymbol.attr.default set attr
        symbol.attr.default.clear()
      }
      symbol.attr.oReg set rSymbol

    case _ =>
  }

  override def transform(tree: Tree): Tree = tree match {
    case ExprSym(symbol) =>
      // Rewrite all references to the registered output
      // port as references to the local reg
      symbol.attr.oReg.get map { rSymbol =>
        ExprSym(rSymbol) regularize tree.loc
      } getOrElse {
        tree
      }

    case EntDecl(decl @ Decl(Sym(oSymbol, _), desc @ DescOut(_, _, StorageTypeReg, initOpt))) =>
      // Change storage type to wire, add register declaration and add connect
      val oDecl = EntDecl(decl.copy(desc = desc.copy(st = StorageTypeWire, initOpt = None)))
      val rSymbol = oSymbol.attr.oReg.value
      val rDecl = EntDecl(rSymbol.decl(initOpt))
      val conn = EntConnect(ExprSym(rSymbol), List(ExprSym(oSymbol)))
      Thicket(List(oDecl, rDecl, conn)) regularize tree.loc

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    tree visit {
      case node @ DescOut(_, _, st, _) if st != StorageTypeWire =>
        cc.ice(node, s"Output port with non-wire storage remains")
    }
  }

}

object LowerRegPorts extends TreeTransformerPass {
  val name = "lower-reg-ports"
  def create(implicit cc: CompilerContext) = new LowerRegPorts
}
