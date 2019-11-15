////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2017-2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Peter de Rivaz/Geza Lore
//
// DESCRIPTION:
//
// AST representation used throughout the compiler
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.core.FlowControlTypes.FlowControlType
import com.argondesign.alogic.core.FuncVariant
import com.argondesign.alogic.core.Locationed
import com.argondesign.alogic.core.StorageTypes.StorageType
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.lib.StructuredTree
import com.argondesign.alogic.util.SequenceNumbers

import scala.collection.mutable

object Trees {

  private[this] val sequenceNumbers = new SequenceNumbers

  //////////////////////////////////////////////////////////////////////////////
  // AST base type
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Tree extends StructuredTree with Locationed with TreeOps {
    val id: Int = sequenceNumbers.next // TODO: Get rid of this
  }

  object Tree extends ObjectTreeOps

  //////////////////////////////////////////////////////////////////////////////
  // Root node (contents of a file)
  //////////////////////////////////////////////////////////////////////////////

  case class Root(body: List[Riz]) extends Tree with RootOps

  //////////////////////////////////////////////////////////////////////////////
  // Ref (reference) nodes refer to names (symbols)
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Ref extends Tree with RefOps

  case class Ident(override val name: String, idxs: List[Expr]) extends Ref with IdentImpl
  case class Sym(override val symbol: Symbol, idxs: List[Expr]) extends Ref

  //////////////////////////////////////////////////////////////////////////////
  // Decl (declaration) nodes introduce names (symbols)
  //////////////////////////////////////////////////////////////////////////////

  // TODO: rename to Defn (definition)
  case class Decl(ref: Ref, desc: Desc) extends Tree with DeclImpl with DeclOps

  //////////////////////////////////////////////////////////////////////////////
  // Desc (description) nodes describe symbols defined in Decl nodes
  //////////////////////////////////////////////////////////////////////////////

  // format: off
  sealed trait Desc extends Tree with DescOps
  
  case class DescVar(spec: Expr, initOpt: Option[Expr]) extends Desc
  case class DescIn(spec: Expr, fc: FlowControlType) extends Desc
  case class DescOut(spec: Expr, fc: FlowControlType, st: StorageType, initOpt: Option[Expr]) extends Desc
  case class DescPipeline(spec: Expr) extends Desc
  case class DescParam(spec: Expr, initOpt: Option[Expr]) extends Desc
  case class DescConst(spec: Expr, init: Expr) extends Desc
  case class DescGen(spec: Expr, init: Expr) extends Desc
  case class DescArray(elem: Expr, size: Expr) extends Desc
  case class DescSram(elem: Expr, size: Expr, st: StorageType) extends Desc
  case class DescStack(elem: Expr, size: Expr) extends Desc
  case class DescType(spec: Expr) extends Desc
  case class DescEntity(variant: EntityVariant.Type, body: List[Ent]) extends Desc with DescEntityOps
  case class DescRecord(body: List[Rec]) extends Desc with DescRecordOps
  case class DescInstance(spec: Expr) extends Desc
  case class DescSingleton(variant: EntityVariant.Type, body: List[Ent]) extends Desc with DescSingletonOps
  case class DescFunc(variant: FuncVariant, ret: Expr, args: List[Decl], body: List[Stmt]) extends Desc with DescFuncOps
  case class DescState(expr: Expr, body: List[Stmt]) extends Desc
  case class DescChoice(choices: List[ExprSym]) extends Desc
  // format: on

  //////////////////////////////////////////////////////////////////////////////
  // Gen constructs
  //////////////////////////////////////////////////////////////////////////////

  // format: off
  sealed trait Gen extends Tree

  case class GenIf(cond: Expr, thenItems: List[Tree], elseItems: List[Tree]) extends Gen
  case class GenFor(decls: List[Decl], cond: Expr, steps: List[Stmt], body: List[Tree]) extends Gen
  case class GenRange(decl: Decl, op: String, end: Expr, body: List[Tree]) extends Gen
  // format: on

  //////////////////////////////////////////////////////////////////////////////
  // Root contents (Riz is from 'riza', the Greek word for root)
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Riz extends Tree

  case class RizDecl(decl: Decl) extends Riz

  //////////////////////////////////////////////////////////////////////////////
  // Entity contents
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Ent extends Tree

  case class EntDecl(decl: Decl) extends Ent
  case class EntGen(gen: Gen) extends Ent
  case class EntConnect(lhs: Expr, rhs: List[Expr]) extends Ent
  case class EntCombProcess(stmts: List[Stmt]) extends Ent
  case class EntVerbatim(lang: String, body: String) extends Ent
  case class EntComment(str: String) extends Ent

  //////////////////////////////////////////////////////////////////////////////
  // Record contents
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Rec extends Tree

  case class RecDecl(decl: Decl) extends Rec
  case class RecGen(gen: Gen) extends Rec
  case class RecComment(str: String) extends Rec

  //////////////////////////////////////////////////////////////////////////////
  // Statements
  //////////////////////////////////////////////////////////////////////////////

  // format: off
  sealed trait Stmt extends Tree

  case class StmtDecl(decl: Decl) extends Stmt
  case class StmtGen(gen: Gen) extends Stmt
  case class StmtBlock(body: List[Stmt]) extends Stmt
  case class StmtIf(cond: Expr, thenStmts: List[Stmt], elseStmts: List[Stmt]) extends Stmt
  case class StmtCase(expr: Expr, cases: List[Case]) extends Stmt
  case class StmtLoop(body: List[Stmt]) extends Stmt
  case class StmtWhile(cond: Expr, body: List[Stmt]) extends Stmt
  case class StmtFor(inits: List[Stmt], cond: Option[Expr], steps: List[Stmt], body: List[Stmt]) extends Stmt
  case class StmtDo(cond: Expr, body: List[Stmt]) extends Stmt
  case class StmtLet(inits: List[Stmt], body: List[Stmt]) extends Stmt
  case class StmtFence() extends Stmt
  case class StmtBreak() extends Stmt
  case class StmtContinue() extends Stmt
  case class StmtGoto(expr: Expr) extends Stmt
  case class StmtReturn() extends Stmt
  case class StmtAssign(lhs: Expr, rhs: Expr) extends Stmt
  case class StmtUpdate(lhs: Expr, op: String, rhs: Expr) extends Stmt
  case class StmtPost(expr: Expr, op: String) extends Stmt
  case class StmtRead() extends Stmt
  case class StmtWrite() extends Stmt
  case class StmtExpr(expr: Expr) extends Stmt
  case class StmtStall(cond: Expr) extends Stmt
  case class StmtError() extends Stmt
  case class StmtComment(str: String) extends Stmt
  // format: on

  //////////////////////////////////////////////////////////////////////////////
  // Case clauses
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Case extends Tree with CaseOps

  case class CaseGen(gen: Gen) extends Case
  case class CaseRegular(cond: List[Expr], override val stmts: List[Stmt]) extends Case
  case class CaseDefault(override val stmts: List[Stmt]) extends Case

  //////////////////////////////////////////////////////////////////////////////
  // Expressions
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Expr extends Tree with ExprOps

  object Expr extends ObjectExprOps

  case class ExprCall(expr: Expr, args: List[Arg]) extends Expr
  case class ExprUnary(op: String, expr: Expr) extends Expr
  case class ExprBinary(lhs: Expr, op: String, rhs: Expr) extends Expr
  case class ExprTernary(cond: Expr, thenExpr: Expr, elseExpr: Expr) extends Expr
  case class ExprRep(count: Expr, expr: Expr) extends Expr
  case class ExprCat(parts: List[Expr]) extends Expr
  case class ExprIndex(expr: Expr, index: Expr) extends Expr
  case class ExprSlice(expr: Expr, lIdx: Expr, op: String, rIdx: Expr) extends Expr
  case class ExprSelect(expr: Expr, selector: String, idxs: List[Expr]) extends Expr
  case class ExprRef(ref: Ref) extends Expr
  case class ExprSym(symbol: Symbol) extends Expr
  case class ExprType(kind: TypeFund) extends Expr
  case class ExprCast(kind: TypeFund, expr: Expr) extends Expr
  case class ExprInt(signed: Boolean, width: Int, value: BigInt) extends Expr with ExprIntImpl
  case class ExprNum(signed: Boolean, value: BigInt) extends Expr with ExprNumImpl
  case class ExprStr(value: String) extends Expr
  case class ExprError() extends Expr

  //////////////////////////////////////////////////////////////////////////////
  // Argument assignments
  //////////////////////////////////////////////////////////////////////////////

  sealed trait Arg extends Tree

  case class ArgP(expr: Expr) extends Arg
  case class ArgN(name: String, expr: Expr) extends Arg

  //////////////////////////////////////////////////////////////////////////////
  // Thicket
  //////////////////////////////////////////////////////////////////////////////

  // Thicket is used where a node needs to be transformed into a list of nodes.
  // Thickets are transient and are flattened into the receiving list during
  // traversal. Any node type T that can be transformed into a Thicket must be
  // held as a List[T] by parent nodes and never as a simple T.
  // These node types include: Stmt, Ent, Rec

  case class Thicket(trees: List[Tree]) extends Tree // TODO: should be a TreeLike...
}

trait IdentImpl { this: Trees.Ident =>
  val attr: mutable.Map[String, Trees.Expr] = mutable.Map()
}

trait DeclImpl { this: Trees.Decl =>
  this.ref match {
    case Trees.Sym(symbol, _) => symbol.decl = this
    case _                    =>
  }
}

trait ExprIntImpl { this: Trees.ExprInt =>
  require(width > 0, s"width=$width")
  require(signed || value >= 0, s"signed=$signed, value=$value")
  require(if (value >= 0) (value >> width) == 0 else (value >> width) == -1,
          s"width=$width, value=$value")
}

trait ExprNumImpl {
  this: Trees.ExprNum =>
  require(signed || value >= 0, s"signed=$signed, value=$value")
}
