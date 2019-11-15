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
// Factory to build sram entities
////////////////////////////////////////////////////////////////////////////////
package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees.StmtAssign
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeNone
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.lib.Math

import scala.util.ChainingSyntax

object SramFactory extends ChainingSyntax {

  /*
    fsm sram {
      in bool ce;
      in bool we;
      in uint($clog2(DEPTH)) addr;
      in uint(WIDTH) wdata;
      out uint(WIDTH) rdata;

      uint(WIDTH) storage[DEPTH];

      void main() {
        if (ce) {
          if (we) {
            stroage.write(addr, wdata);
            rdata = 0; // Or anything really
          } else {
            rdata = storage[addr];
          }
        }
        fence;
      }
    }

   */

  def apply(
      name: String,
      loc: Loc,
      width: Int,
      depth: Int
  )(
      implicit cc: CompilerContext
  ): Decl = {

    val fcn = FlowControlTypeNone

    val addrKind = TypeUInt(Math.clog2(depth))
    val dataKind = TypeUInt(width)

    val ceSymbol = cc.newSymbol("ce", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val weSymbol = cc.newSymbol("we", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val adSymbol = cc.newSymbol("addr", loc) tap { _.kind = TypeIn(addrKind, fcn) }
    val wdSymbol = cc.newSymbol("wdata", loc) tap { _.kind = TypeIn(dataKind, fcn) }
    val rdSymbol = cc.newSymbol("rdata", loc) tap {
      _.kind = TypeOut(dataKind, fcn, StorageTypeReg)
    }
    val stSymbol = cc.newSymbol("storage", loc) tap { _.kind = TypeArray(dataKind, depth) }

    val ceDecl = ceSymbol.decl
    val weDecl = weSymbol.decl
    val adDecl = adSymbol.decl
    val wdDecl = wdSymbol.decl
    val rdDecl = rdSymbol.decl
    val stDecl = stSymbol.decl

    val ceRef = ExprSym(ceSymbol)
    val weRef = ExprSym(weSymbol)
    val adRef = ExprSym(adSymbol)
    val wdRef = ExprSym(wdSymbol)
    val rdRef = ExprSym(rdSymbol)
    val stRef = ExprSym(stSymbol)

    val statements = List(
      StmtIf(
        ceRef,
        List(
          StmtIf(
            weRef,
            List(
              StmtExpr(ExprCall(stRef select "write", List(ArgP(adRef), ArgP(wdRef)))),
              StmtAssign(rdRef, ExprInt(false, width, 0))
            ),
            List(
              StmtAssign(rdRef, stRef index adRef)
            )
          )
        ),
        Nil
      )
    )

    val decls = List(ceDecl, weDecl, adDecl, wdDecl, rdDecl, stDecl) map EntDecl

    val desc = DescEntity(EntityVariant.Fsm, decls ::: EntCombProcess(statements) :: Nil)
    val entitySymbol = cc.newSymbol(name, loc)
    entitySymbol.attr.sram set true
    Decl(Sym(entitySymbol, Nil), desc) regularize loc tap { _ =>
      entitySymbol.attr.highLevelKind set entitySymbol.kind.asType.kind.asEntity
    }
  }

}
