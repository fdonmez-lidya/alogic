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
// Tree copier used in tree transformations to only perform copying if required
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.ast.Trees._

// scalastyle:off token

// Given a Tree and new child nodes, create new Tree if children are not the same as
// the children of the current Tree, otherwise reuse existing Tree. Note that only
// fields containing Tree instances are checked as other fields are not transformed
// recursively in TreeTransformer
object TreeCopier {

  //////////////////////////////////////////////////////////////////////////////
  // Root
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: Root)(body: List[Tree]): Root = {
    if (body eq tree.body) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Riz] })
      Root(body.asInstanceOf[List[Riz]]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Ref
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: Ident)(indices: List[Tree]): Ident = {
    if (indices eq tree.idxs) {
      tree
    } else {
      assert(indices forall { _.isInstanceOf[Expr] })
      Ident(tree.name, indices.asInstanceOf[List[Expr]]) withLoc tree.loc
    }
  }

  def apply(tree: Sym)(indices: List[Tree]): Sym = {
    if (indices eq tree.idxs) {
      tree
    } else {
      assert(indices forall { _.isInstanceOf[Expr] })
      Sym(tree.symbol, indices.asInstanceOf[List[Expr]]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Decl
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: Decl)(ref: Tree, desc: Tree): Decl = {
    if ((ref eq tree.ref) && (desc eq tree.desc)) {
      tree
    } else {
      Decl(ref.asInstanceOf[Ref], desc.asInstanceOf[Desc]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Desc
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: DescVar)(spec: Tree, initOpt: Option[Tree]): DescVar = {
    if ((spec eq tree.spec) && (initOpt eq tree.initOpt)) {
      tree
    } else {
      assert(initOpt forall { _.isInstanceOf[Expr] })
      DescVar(spec.asInstanceOf[Expr], initOpt.asInstanceOf[Option[Expr]]) withLoc tree.loc
    }
  }

  def apply(tree: DescIn)(spec: Tree): DescIn = {
    if (spec eq tree.spec) {
      tree
    } else {
      tree.copy(spec = spec.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescOut)(spec: Tree, initOpt: Option[Tree]): DescOut = {
    if ((spec eq tree.spec) && (initOpt eq tree.initOpt)) {
      tree
    } else {
      assert(initOpt forall { _.isInstanceOf[Expr] })
      tree.copy(
        spec = spec.asInstanceOf[Expr],
        initOpt = initOpt.asInstanceOf[Option[Expr]]
      ) withLoc tree.loc
    }
  }

  def apply(tree: DescPipeline)(spec: Tree): DescPipeline = {
    if (spec eq tree.spec) {
      tree
    } else {
      DescPipeline(spec.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescParam)(spec: Tree, initOpt: Option[Tree]): DescParam = {
    if ((spec eq tree.spec) && (initOpt eq tree.initOpt)) {
      tree
    } else {
      assert(initOpt forall { _.isInstanceOf[Expr] })
      DescParam(
        spec.asInstanceOf[Expr],
        initOpt.asInstanceOf[Option[Expr]]
      ) withLoc tree.loc
    }
  }

  def apply(tree: DescConst)(spec: Tree, init: Tree): DescConst = {
    if ((spec eq tree.spec) && (init eq tree.init)) {
      tree
    } else {
      DescConst(spec.asInstanceOf[Expr], init.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescGen)(spec: Tree, init: Tree): DescGen = {
    if ((spec eq tree.spec) && (init eq tree.init)) {
      tree
    } else {
      DescGen(spec.asInstanceOf[Expr], init.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescArray)(elem: Tree, size: Tree): DescArray = {
    if ((elem eq tree.elem) && (size eq tree.size)) {
      tree
    } else {
      DescArray(elem.asInstanceOf[Expr], size.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescSram)(elem: Tree, size: Tree): DescSram = {
    if ((elem eq tree.elem) && (size eq tree.size)) {
      tree
    } else {
      tree.copy(
        elem = elem.asInstanceOf[Expr],
        size = size.asInstanceOf[Expr]
      ) withLoc tree.loc
    }
  }

  def apply(tree: DescStack)(elem: Tree, size: Tree): DescStack = {
    if ((elem eq tree.elem) && (size eq tree.size)) {
      tree
    } else {
      DescStack(elem.asInstanceOf[Expr], size.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescType)(spec: Tree): DescType = {
    if (spec eq tree.spec) {
      tree
    } else {
      DescType(spec.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescEntity)(body: List[Tree]): DescEntity = {
    if (body eq tree.body) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Ent] })
      tree.copy(body = body.asInstanceOf[List[Ent]]) withLoc tree.loc
    }
  }

  def apply(tree: DescRecord)(body: List[Tree]): DescRecord = {
    if (body eq tree.body) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Rec] })
      DescRecord(body.asInstanceOf[List[Rec]]) withLoc tree.loc
    }
  }

  def apply(tree: DescInstance)(spec: Tree): DescInstance = {
    if (spec eq tree.spec) {
      tree
    } else {
      DescInstance(spec.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: DescSingleton)(body: List[Tree]): DescSingleton = {
    if (body eq tree.body) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Ent] })
      tree.copy(body = body.asInstanceOf[List[Ent]]) withLoc tree.loc
    }
  }

  def apply(tree: DescFunc)(ret: Tree, args: List[Tree], body: List[Tree]): DescFunc = {
    if ((ret eq tree.ret) && (args eq tree.args) && (body eq tree.body)) {
      tree
    } else {
      assert(args forall { _.isInstanceOf[Decl] })
      assert(body forall { _.isInstanceOf[Stmt] })
      tree.copy(
        ret = ret.asInstanceOf[Expr],
        args = args.asInstanceOf[List[Decl]],
        body = body.asInstanceOf[List[Stmt]]
      ) withLoc tree.loc
    }
  }

  def apply(tree: DescState)(expr: Tree, body: List[Tree]): DescState = {
    if ((expr eq tree.expr) && (body eq tree.body)) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Stmt] })
      DescState(expr.asInstanceOf[Expr], body.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: DescChoice)(choices: List[Tree]): DescChoice = {
    if (choices eq tree.choices) {
      tree
    } else {
      assert(choices forall { _.isInstanceOf[ExprSym] })
      DescChoice(choices.asInstanceOf[List[ExprSym]]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Gen
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: GenIf)(cond: Tree, thenItems: List[Tree], elseItems: List[Tree]): GenIf = {
    if ((cond eq tree.cond) && (thenItems eq tree.thenItems) && (elseItems eq tree.elseItems)) {
      tree
    } else {
      GenIf(
        cond.asInstanceOf[Expr],
        thenItems.asInstanceOf[List[Stmt]],
        elseItems.asInstanceOf[List[Stmt]]
      ) withLoc tree.loc
    }
  }

  def apply(
      tree: GenFor
  )(
      decls: List[Tree],
      cond: Tree,
      steps: List[Tree],
      body: List[Tree]
  ): GenFor = {
    if ((decls eq tree.decls) && (cond eq tree.cond) && (steps eq tree.steps) && (body eq tree.body)) {
      tree
    } else {
      assert(decls forall { _.isInstanceOf[Decl] })
      assert(steps forall { _.isInstanceOf[Stmt] })
      GenFor(
        decls.asInstanceOf[List[Decl]],
        cond.asInstanceOf[Expr],
        steps.asInstanceOf[List[Stmt]],
        body
      ) withLoc tree.loc
    }
  }

  def apply(tree: GenRange)(decl: Tree, end: Tree, body: List[Tree]): GenRange = {
    if ((decl eq tree.decl) && (end eq tree.end) && (body eq tree.body)) {
      tree
    } else {
      tree.copy(
        decl = decl.asInstanceOf[Decl],
        end = end.asInstanceOf[Expr],
        body = body
      ) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Riz
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: RizDecl)(decl: Tree): RizDecl = {
    if (decl eq tree.decl) {
      tree
    } else {
      RizDecl(decl.asInstanceOf[Decl]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Ent
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: EntDecl)(decl: Tree): EntDecl = {
    if (decl eq tree.decl) {
      tree
    } else {
      EntDecl(decl.asInstanceOf[Decl]) withLoc tree.loc
    }
  }

  def apply(tree: EntGen)(gen: Tree): EntGen = {
    if (gen eq tree.gen) {
      tree
    } else {
      EntGen(gen.asInstanceOf[Gen]) withLoc tree.loc
    }
  }

  def apply(tree: EntConnect)(lhs: Tree, rhs: List[Tree]): EntConnect = {
    if ((lhs eq tree.lhs) && (rhs eq tree.rhs)) {
      tree
    } else {
      assert(rhs forall { _.isInstanceOf[Expr] })
      EntConnect(lhs.asInstanceOf[Expr], rhs.asInstanceOf[List[Expr]]) withLoc tree.loc
    }
  }

  def apply(tree: EntCombProcess)(stmts: List[Tree]): EntCombProcess = {
    if (stmts eq tree.stmts) {
      tree
    } else {
      assert(stmts forall { _.isInstanceOf[Stmt] })
      EntCombProcess(stmts.asInstanceOf[List[StmtIf]]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Rec
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: RecDecl)(decl: Tree): RecDecl = {
    if (decl eq tree.decl) {
      tree
    } else {
      RecDecl(decl.asInstanceOf[Decl]) withLoc tree.loc
    }
  }

  def apply(tree: RecGen)(gen: Tree): RecGen = {
    if (gen eq tree.gen) {
      tree
    } else {
      RecGen(gen.asInstanceOf[Gen]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Stmt
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: StmtDecl)(decl: Tree): StmtDecl = {
    if (decl eq tree.decl) {
      tree
    } else {
      StmtDecl(decl.asInstanceOf[Decl]) withLoc tree.loc
    }
  }

  def apply(tree: StmtGen)(gen: Tree): StmtGen = {
    if (gen eq tree.gen) {
      tree
    } else {
      StmtGen(gen.asInstanceOf[Gen]) withLoc tree.loc
    }
  }

  def apply(tree: StmtBlock)(body: List[Tree]): StmtBlock = {
    if (body eq tree.body) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Stmt] })
      StmtBlock(body.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: StmtIf)(
      cond: Tree,
      thenStmts: List[Tree],
      elseStmts: List[Tree]
  ): StmtIf = {
    if ((cond eq tree.cond) && (thenStmts eq tree.thenStmts) && (elseStmts eq tree.elseStmts)) {
      tree
    } else {
      assert(thenStmts forall { _.isInstanceOf[Stmt] })
      assert(elseStmts forall { _.isInstanceOf[Stmt] })
      StmtIf(
        cond.asInstanceOf[Expr],
        thenStmts.asInstanceOf[List[Stmt]],
        elseStmts.asInstanceOf[List[Stmt]]
      ) withLoc tree.loc
    }
  }

  def apply(tree: StmtCase)(expr: Tree, cases: List[Tree]): StmtCase = {
    if ((expr eq tree.expr) && (cases eq tree.cases)) {
      tree
    } else {
      assert(cases forall { _.isInstanceOf[Case] })
      StmtCase(
        expr.asInstanceOf[Expr],
        cases.asInstanceOf[List[Case]],
      ) withLoc tree.loc
    }
  }

  def apply(tree: StmtLoop)(body: List[Tree]): StmtLoop = {
    if (body eq tree.body) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Stmt] })
      StmtLoop(body.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: StmtWhile)(cond: Tree, body: List[Tree]): StmtWhile = {
    if ((cond eq tree.cond) && (body eq tree.body)) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Stmt] })
      StmtWhile(cond.asInstanceOf[Expr], body.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(
      tree: StmtFor
  )(
      inits: List[Tree],
      cond: Option[Tree],
      steps: List[Tree],
      body: List[Tree]
  ): StmtFor = {
    if ((inits eq tree.inits) && (cond eq tree.cond) && (steps eq tree.steps) && (body eq tree.body)) {
      tree
    } else {
      assert(inits forall { _.isInstanceOf[Stmt] })
      assert(cond forall { _.isInstanceOf[Expr] })
      assert(steps forall { _.isInstanceOf[Stmt] })
      assert(body forall { _.isInstanceOf[Stmt] })
      StmtFor(
        inits.asInstanceOf[List[Stmt]],
        cond.asInstanceOf[Option[Expr]],
        steps.asInstanceOf[List[Stmt]],
        body.asInstanceOf[List[Stmt]]
      ) withLoc tree.loc
    }
  }

  def apply(tree: StmtDo)(cond: Tree, body: List[Tree]): StmtDo = {
    if ((cond eq tree.cond) && (body eq tree.body)) {
      tree
    } else {
      assert(body forall { _.isInstanceOf[Stmt] })
      StmtDo(cond.asInstanceOf[Expr], body.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: StmtLet)(inits: List[Tree], body: List[Tree]): StmtLet = {
    if ((inits eq tree.inits) && (body eq tree.body)) {
      tree
    } else {
      assert(inits forall { _.isInstanceOf[Stmt] })
      assert(body forall { _.isInstanceOf[Stmt] })
      StmtLet(inits.asInstanceOf[List[Stmt]], body.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: StmtGoto)(expr: Tree): StmtGoto = {
    if (expr eq tree.expr) {
      tree
    } else {
      StmtGoto(expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: StmtAssign)(lhs: Tree, rhs: Tree): StmtAssign = {
    if ((lhs eq tree.lhs) && (rhs eq tree.rhs)) {
      tree
    } else {
      StmtAssign(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: StmtUpdate)(lhs: Tree, rhs: Tree): StmtUpdate = {
    if ((lhs eq tree.lhs) && (rhs eq tree.rhs)) {
      tree
    } else {
      StmtUpdate(lhs.asInstanceOf[Expr], tree.op, rhs.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: StmtPost)(expr: Tree): StmtPost = {
    if (expr eq tree.expr) {
      tree
    } else {
      StmtPost(expr.asInstanceOf[Expr], tree.op) withLoc tree.loc
    }
  }

  def apply(tree: StmtExpr)(expr: Tree): StmtExpr = {
    if (expr eq tree.expr) {
      tree
    } else {
      StmtExpr(expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: StmtStall)(cond: Tree): StmtStall = {
    if (cond eq tree.cond) {
      tree
    } else {
      StmtStall(cond.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Case
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: CaseRegular)(cond: List[Tree], stmts: List[Tree]): CaseRegular = {
    if ((cond eq tree.cond) && (stmts eq tree.stmts)) {
      tree
    } else {
      assert(cond forall { _.isInstanceOf[Expr] })
      assert(stmts forall { _.isInstanceOf[Stmt] })
      CaseRegular(cond.asInstanceOf[List[Expr]], stmts.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: CaseDefault)(stmts: List[Tree]): CaseDefault = {
    if (stmts eq tree.stmts) {
      tree
    } else {
      assert(stmts forall { _.isInstanceOf[Stmt] })
      CaseDefault(stmts.asInstanceOf[List[Stmt]]) withLoc tree.loc
    }
  }

  def apply(tree: CaseGen)(gen: Tree): CaseGen = {
    if (gen eq tree.gen) {
      tree
    } else {
      CaseGen(gen.asInstanceOf[Gen]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Expr
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: ExprCall)(expr: Tree, args: List[Tree]): ExprCall = {
    if ((expr eq tree.expr) && (args eq tree.args)) {
      tree
    } else {
      assert(args forall { _.isInstanceOf[Arg] })
      ExprCall(expr.asInstanceOf[Expr], args.asInstanceOf[List[Arg]]) withLoc tree.loc
    }
  }

  def apply(tree: ExprUnary)(expr: Tree): ExprUnary = {
    if (expr eq tree.expr) {
      tree
    } else {
      tree.copy(expr = expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: ExprBinary)(lhs: Tree, rhs: Tree): ExprBinary = {
    if ((lhs eq tree.lhs) && (rhs eq tree.rhs)) {
      tree
    } else {
      tree.copy(lhs = lhs.asInstanceOf[Expr], rhs = rhs.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: ExprTernary)(cond: Tree, thenExpr: Tree, elseExpr: Tree): ExprTernary = {
    if ((cond eq tree.cond) && (thenExpr eq tree.thenExpr) && (elseExpr eq tree.elseExpr)) {
      tree
    } else {
      ExprTernary(cond.asInstanceOf[Expr], thenExpr.asInstanceOf[Expr], elseExpr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: ExprRep)(count: Tree, expr: Tree): ExprRep = {
    if ((count eq tree.count) && (expr eq tree.expr)) {
      tree
    } else {
      ExprRep(count.asInstanceOf[Expr], expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: ExprCat)(parts: List[Tree]): ExprCat = {
    if (parts eq tree.parts) {
      tree
    } else {
      assert(parts forall { _.isInstanceOf[Expr] })
      ExprCat(parts.asInstanceOf[List[Expr]]) withLoc tree.loc
    }
  }

  def apply(tree: ExprIndex)(expr: Tree, index: Tree): ExprIndex = {
    if ((expr eq tree.expr) && (index eq tree.index)) {
      tree
    } else {
      ExprIndex(expr.asInstanceOf[Expr], index.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: ExprSlice)(expr: Tree, lIdx: Tree, rIdx: Tree): ExprSlice = {
    if ((expr eq tree.expr) && (lIdx eq tree.lIdx) && (rIdx eq tree.rIdx)) {
      tree
    } else {
      tree.copy(
        expr = expr.asInstanceOf[Expr],
        lIdx = lIdx.asInstanceOf[Expr],
        rIdx = rIdx.asInstanceOf[Expr]
      ) withLoc tree.loc
    }
  }

  def apply(tree: ExprSelect)(expr: Tree, idxs: List[Tree]): ExprSelect = {
    if ((expr eq tree.expr) && (idxs eq tree.idxs)) {
      tree
    } else {
      assert(idxs forall { _.isInstanceOf[Expr] })
      tree.copy(
        expr = expr.asInstanceOf[Expr],
        idxs = idxs.asInstanceOf[List[Expr]]
      ) withLoc tree.loc
    }
  }

  def apply(tree: ExprRef)(ref: Tree): ExprRef = {
    if (ref eq tree.ref) {
      tree
    } else {
      ExprRef(ref.asInstanceOf[Ref]) withLoc tree.loc
    }
  }

  def apply(tree: ExprCast)(expr: Tree): ExprCast = {
    if (expr eq tree.expr) {
      tree
    } else {
      tree.copy(expr = expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Arg
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: ArgP)(expr: Tree): ArgP = {
    if (expr eq tree.expr) {
      tree
    } else {
      ArgP(expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  def apply(tree: ArgN)(expr: Tree): ArgN = {
    if (expr eq tree.expr) {
      tree
    } else {
      tree.copy(expr = expr.asInstanceOf[Expr]) withLoc tree.loc
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Thicket
  //////////////////////////////////////////////////////////////////////////////

  def apply(tree: Thicket)(trees: List[Tree]): Thicket = {
    if (trees eq tree.trees) {
      tree
    } else {
      Thicket(trees) withLoc tree.loc
    }
  }

}
