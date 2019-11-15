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
// Factory to build output register entities
////////////////////////////////////////////////////////////////////////////////
package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeNone
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant

import scala.util.ChainingSyntax

object SyncRegFactory extends ChainingSyntax {

  /*

  // Register slice interface

  // Hardware interface:
  _ip
  _ip_valid

  _op
  _op_valid

  at beginning:
  _ip_valid = 1'b0

   */

  // Build an entity similar to the following Alogic FSM to be used as an
  // output register implementation. The body of the main function is filled
  // in by the above implementations.
  //
  // fsm sync_reg {
  //   // Upstream interface
  //   in payload_t ip;
  //   in bool ip_valid;
  //
  //   // Downstream interface
  //   out wire payload_t op;
  //   out wire bool op_valid;
  //
  //   // Local storage
  //   payload_t payload;
  //   bool valid = false;
  //
  //   void main() {
  //     if (ip_valid) {
  //       payload = ip;
  //     }
  //     valid = ip_valid;
  //   }
  //
  //   payload -> op;
  //   valid -> op_valid;
  // }
  private def buildSyncReg(
      name: String,
      loc: Loc,
      kind: TypeFund,
      sep: String
  )(
      implicit cc: CompilerContext
  ): Decl = {
    val fcn = FlowControlTypeNone
    val stw = StorageTypeWire

    lazy val ipSymbol = cc.newSymbol("ip", loc) tap { _.kind = TypeIn(kind, fcn) }
    val ipvSymbol = cc.newSymbol(s"ip${sep}valid", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    lazy val opSymbol = cc.newSymbol("op", loc) tap { _.kind = TypeOut(kind, fcn, stw) }
    val opvSymbol = cc.newSymbol(s"op${sep}valid", loc) tap {
      _.kind = TypeOut(TypeUInt(1), fcn, stw)
    }
    lazy val pSymbol = cc.newSymbol("payload", loc) tap { _.kind = kind }
    val vSymbol = cc.newSymbol("valid", loc) tap { _.kind = TypeUInt(1) }

    lazy val ipDecl = ipSymbol.decl
    val ipvDecl = ipvSymbol.decl
    lazy val opDecl = opSymbol.decl
    val opvDecl = opvSymbol.decl
    lazy val pDecl = pSymbol.decl
    val vDecl = vSymbol.decl(ExprInt(false, 1, 0))

    lazy val ipRef = ExprSym(ipSymbol)
    val ipvRef = ExprSym(ipvSymbol)
    lazy val opRef = ExprSym(opSymbol)
    val opvRef = ExprSym(opvSymbol)
    lazy val pRef = ExprSym(pSymbol)
    val vRef = ExprSym(vSymbol)

    val statements = if (kind != TypeVoid) {
      List(
        StmtIf(
          ipvRef,
          List(StmtAssign(pRef, ipRef)),
          Nil
        ),
        StmtAssign(vRef, ipvRef)
      )
    } else {
      List(StmtAssign(vRef, ipvRef))
    }

    val decls = {
      if (kind != TypeVoid) {
        List(ipDecl, ipvDecl, opDecl, opvDecl, pDecl, vDecl)
      } else {
        List(ipvDecl, opvDecl, vDecl)
      }
    } map {
      EntDecl
    }

    val connects = if (kind != TypeVoid) {
      List(
        EntConnect(pRef, List(opRef)),
        EntConnect(vRef, List(opvRef))
      )
    } else {
      List(
        EntConnect(vRef, List(opvRef))
      )
    }

    val entitySymbol = cc.newSymbol(name, loc)
    val desc = DescEntity(EntityVariant.Fsm, decls ::: EntCombProcess(statements) :: connects)
    Decl(Sym(entitySymbol, Nil), desc) regularize loc tap { _ =>
      entitySymbol.attr.highLevelKind set entitySymbol.kind.asType.kind.asEntity
    }
  }

  def apply(
      name: String,
      loc: Loc,
      kind: TypeFund
  )(
      implicit cc: CompilerContext
  ): Decl = {
    require(kind.isPacked)
    buildSyncReg(name, loc, kind, cc.sep)
  }

}
