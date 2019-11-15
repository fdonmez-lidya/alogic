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
// Factory to build stack entities
////////////////////////////////////////////////////////////////////////////////
package com.argondesign.alogic.core

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeNone
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.lib.Math

import scala.util.ChainingSyntax

object StackFactory extends ChainingSyntax {

  /*

  // Hardware stack interface

  stack<i8>(10) s;

  s.push(addr); // i8 => void
  s.pop();      // void => i8
  s.set(addr);  // i8 => void // Same as 's = addr' if s is an automatic variable
  s.top;        // i8 // Same as 's' if s is an automatic variable
  s.full;       // bool
  s.empty;      // bool

  restrictions:
   - Can only do a single push, pop, or set in the same cycle, compiler should err otherwise
   - .push() when full is error
   - .pop() when empty is error
   - .top when empty is error

  // Function call/return handling ('rs' is for 'return-stack':

  foo();    // maps to rs.push(return-state); goto foo;
  goto foo; // nothing to do here, just goto foo;
  return;   // maps to goto rs.pop();

  // Function argument handling

  At call site: arg.push(value)
  At exit: arg.pop()

  // Function local variable handling

  At definition of variable: local.push(initializer)
  At death/exit from function: local.pop()

  // Hardware interface:

  _en
  _d
  _q

  _push
  _pop
  _full
  _empty

  at beginning:
  _en = 1'b0

   */

  // Build an entity similar to the following Alogic FSM to be used as a
  // 1 entry stack implementation.
  //
  // fsm stack_1 {
  //   in bool en;
  //
  //   in TYPE d;
  //   in bool push;
  //   in bool pop;
  //
  //   out wire TYPE q;
  //   out wire bool empty;
  //   out wire bool full;
  //
  //   bool valid = false;
  //
  //   TYPE storage;
  //
  //   void main() {
  //     if (en) {
  //       storage = d;
  //       valid = ~pop & (valid | push);
  //     }
  //     fence;
  //   }
  //
  //  ~valid -> empty;
  //  valid -> full;
  //  storage -> q;
  // }
  private def buildStack1(
      name: String,
      loc: Loc,
      kind: TypeFund
  )(
      implicit cc: CompilerContext
  ): Decl = {
    val fcn = FlowControlTypeNone
    val stw = StorageTypeWire

    val enSymbol = cc.newSymbol("en", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val pusSymbol = cc.newSymbol("push", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val popSymbol = cc.newSymbol("pop", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val dSymbol = cc.newSymbol("d", loc) tap { _.kind = TypeIn(kind, fcn) }
    val empSymbol = cc.newSymbol("empty", loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, stw) }
    val fulSymbol = cc.newSymbol("full", loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, stw) }
    val qSymbol = cc.newSymbol("q", loc) tap { _.kind = TypeOut(kind, fcn, stw) }
    val valSymbol = cc.newSymbol("valid", loc) tap { _.kind = TypeUInt(1) }
    val stoSymbol = cc.newSymbol("storage", loc) tap { _.kind = kind }

    val enDecl = enSymbol.decl
    val pusDecl = pusSymbol.decl
    val popDecl = popSymbol.decl
    val dDecl = dSymbol.decl
    val empDecl = empSymbol.decl
    val fulDecl = fulSymbol.decl
    val qDecl = qSymbol.decl
    val valDecl = valSymbol.decl(ExprInt(false, 1, 0))
    val stoDecl = stoSymbol.decl

    val enRef = ExprSym(enSymbol)
    val pusRef = ExprSym(pusSymbol)
    val popRef = ExprSym(popSymbol)
    val dRef = ExprSym(dSymbol)
    val empRef = ExprSym(empSymbol)
    val fulRef = ExprSym(fulSymbol)
    val qRef = ExprSym(qSymbol)
    val valRef = ExprSym(valSymbol)
    val stoRef = ExprSym(stoSymbol)

    val statements = List(
      StmtIf(enRef,
             List(
               StmtAssign(stoRef, dRef),
               StmtAssign(valRef, ~popRef & (valRef | pusRef))
             ),
             Nil)
    )

    val decls = List(enDecl, pusDecl, popDecl, dDecl, empDecl, fulDecl, qDecl, valDecl, stoDecl) map {
      EntDecl
    }

    val connects = List(
      EntConnect(~valRef, List(empRef)),
      EntConnect(valRef, List(fulRef)),
      EntConnect(stoRef, List(qRef))
    )

    val desc = DescEntity(EntityVariant.Fsm, decls ::: EntCombProcess(statements) :: connects)
    val entitySymbol = cc.newSymbol(name, loc)
    Decl(Sym(entitySymbol, Nil), desc) regularize loc tap { _ =>
      entitySymbol.attr.highLevelKind set entitySymbol.kind.asType.kind.asEntity
    }
  }

  // Build an entity similar to the following Alogic FSM to be used as an
  // N entry stack implementation with N >= 2.
  //
  // fsm stack_N {
  //   const DEPTH; // > 1
  //
  //   in bool en;
  //
  //   in TYPE d;
  //   in bool push;
  //   in bool pop;
  //
  //   out wire TYPE q;
  //   out bool empty = true;
  //   out bool full = false;
  //
  //   TYPE storage[DEPTH];
  //
  //   uint($clog2(DEPTH)) ptr = 0; // Ptr to current entry
  //
  //   state main {
  //     if (en) {
  //       if (pop) {
  //         empty = ptr == 0;
  //         full = false;
  //         ptr = ptr - ~empty;
  //       } else {
  //         ptr = ptr + (~empty & ~full & push);
  //         storage.write(ptr, d);
  //         empty = empty & ~push;
  //         full = ptr == DEPTH - 1;
  //       }
  //     }
  //     fence;
  //   }
  //
  //   storage[ptr] -> q;
  // }
  private def buildStackN(
      name: String,
      loc: Loc,
      kind: TypeFund,
      depth: BigInt
  )(
      implicit cc: CompilerContext
  ): Decl = {
    require(depth >= 2)

    val fcn = FlowControlTypeNone
    val stw = StorageTypeWire
    val str = StorageTypeReg

    val ptrWidth = Math.clog2(depth)

    val enSymbol = cc.newSymbol("en", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val pusSymbol = cc.newSymbol("push", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val popSymbol = cc.newSymbol("pop", loc) tap { _.kind = TypeIn(TypeUInt(1), fcn) }
    val dSymbol = cc.newSymbol("d", loc) tap { _.kind = TypeIn(kind, fcn) }
    val empSymbol = cc.newSymbol("empty", loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, str) }
    val fulSymbol = cc.newSymbol("full", loc) tap { _.kind = TypeOut(TypeUInt(1), fcn, str) }
    val qSymbol = cc.newSymbol("q", loc) tap { _.kind = TypeOut(kind, fcn, stw) }
    val stoSymbol = cc.newSymbol("storage", loc) tap { _.kind = TypeArray(kind, depth) }
    val ptrSymbol = cc.newSymbol("ptr", loc) tap { _.kind = TypeUInt(ptrWidth) }

    val enDecl = enSymbol.decl
    val pusDecl = pusSymbol.decl
    val popDecl = popSymbol.decl
    val dDecl = dSymbol.decl
    val empDecl = empSymbol.decl(ExprInt(false, 1, 1))
    val fulDecl = fulSymbol.decl(ExprInt(false, 1, 0))
    val qDecl = qSymbol.decl
    val stoDecl = stoSymbol.decl
    val ptrDecl = ptrSymbol.decl(ExprInt(false, ptrWidth, 0))

    val enRef = ExprSym(enSymbol)
    val pusRef = ExprSym(pusSymbol)
    val popRef = ExprSym(popSymbol)
    val dRef = ExprSym(dSymbol)
    val empRef = ExprSym(empSymbol)
    val fulRef = ExprSym(fulSymbol)
    val qRef = ExprSym(qSymbol)
    val stoRef = ExprSym(stoSymbol)
    val ptrRef = ExprSym(ptrSymbol)

    def zextPtrWidth(bool: Expr): Expr = {
      if (ptrWidth == 1) {
        bool
      } else {
        ExprCat(List(ExprInt(false, ptrWidth - 1, 0), bool))
      }
    }

    val statements = List(
      StmtIf(
        enRef,
        List(
          StmtIf(
            popRef,
            List(
              StmtAssign(empRef, ExprBinary(ptrRef, "==", ExprInt(false, ptrWidth, 0))),
              StmtAssign(fulRef, ExprInt(false, 1, 0)),
              StmtAssign(ptrRef, ptrRef - zextPtrWidth(~empRef))
            ),
            List(
              StmtAssign(ptrRef, ptrRef + zextPtrWidth(~empRef & ~fulRef & pusRef)),
              StmtExpr(ExprCall(stoRef select "write", List(ArgP(ptrRef), ArgP(dRef)))),
              StmtAssign(empRef, empRef & ~pusRef),
              StmtAssign(fulRef, ExprBinary(ptrRef, "==", ExprInt(false, ptrWidth, depth - 1)))
            )
          )
        ),
        Nil
      )
    )

    val decls = List(enDecl, pusDecl, popDecl, dDecl, empDecl, fulDecl, qDecl, stoDecl, ptrDecl) map {
      EntDecl
    }

    val connects = List(
      EntConnect(ExprIndex(stoRef, ptrRef), List(qRef))
    )

    val desc = DescEntity(EntityVariant.Fsm, decls ::: EntCombProcess(statements) :: connects)
    val entitySymbol = cc.newSymbol(name, loc)
    Decl(Sym(entitySymbol, Nil), desc) regularize loc tap { _ =>
      entitySymbol.attr.highLevelKind set entitySymbol.kind.asType.kind.asEntity
    }
  }

  def apply(
      name: String,
      loc: Loc,
      kind: TypeFund,
      depth: BigInt
  )(
      implicit cc: CompilerContext
  ): Decl = {
    require(kind.isPacked)
    require(kind != TypeVoid)

    if (depth == 1) {
      buildStack1(name, loc, kind)
    } else {
      buildStackN(name, loc, kind, depth)
    }
  }

}
