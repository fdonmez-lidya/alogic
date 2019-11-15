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
// A Tree transformer used to modify Trees
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.lib.TreeLikeTransformer
import com.argondesign.alogic.typer.TypeAssigner

import scala.collection.mutable

// Tree transformers are applied during a post-order traversal of a Tree.
abstract class TreeTransformer(implicit cc: CompilerContext) extends TreeLikeTransformer[Tree] {

  val typed: Boolean = true

  //////////////////////////////////////////////////////////////////////////////
  // Tree position tracker
  //////////////////////////////////////////////////////////////////////////////

  // The Symbol representing the currently processed entity
  protected[this] def entitySymbol: Symbol = entityStack.top

  private[this] val entityStack = mutable.Stack[Symbol]()

  //////////////////////////////////////////////////////////////////////////////
  // Internals
  //////////////////////////////////////////////////////////////////////////////

  // Walk list, flatten Thickets
  final override def walk(trees: List[Tree]): List[Tree] = {
    val newTrees = super.walk(trees)
    if (newTrees eq trees) {
      trees
    } else {
      newTrees flatMap {
        case Thicket(ts) => ts
        case t: Tree     => List(t)
      }
    }
  }

  final def doTransform(tree: Tree): Tree = {
    // Nodes with children that have been rewritten and henceforth
    // been copied by TreeCopier need their types assigned
    if (typed && !tree.hasTpe) {
      TypeAssigner(tree)
    }

    // Transform the node
    val result = transform(tree)

    assert(tree.hasLoc, this.getClass.getName)

    if (!result.hasLoc) {
      cc.ice(s"Pass '${this.getClass.getName}' lost location of transformed node:",
             result.toString,
             "original at:",
             tree.loc.prefix,
             tree.toString)
    }

    // Check it has type
    if (typed && !result.hasTpe) {
      cc.ice(s"Pass '${this.getClass.getName}' lost type of transformed node:",
             result.toString,
             "original at:",
             tree.loc.prefix,
             tree.toString)
    }

    result
  }

  final override def walk(tree: Tree): Tree = {
    val pushEntity = tree match {
      case Decl(Sym(symbol, _), _: DescEntity) => Some(symbol)
      case _                                   => None
    }
    pushEntity foreach { symbol =>
      entityStack.push(symbol)
    }
    // Check skip in pre order
    val result = if (skip(tree)) {
      tree
    } else {
      // Call enter in pre order
      enter(tree)
      // Call transform in post order
      tree match {
        ////////////////////////////////////////////////////////////////////////
        // Root
        ////////////////////////////////////////////////////////////////////////
        case node: Root =>
          val body = walk(node.body)
          doTransform(TreeCopier(node)(body))
        ////////////////////////////////////////////////////////////////////////
        // Ref
        ////////////////////////////////////////////////////////////////////////
        case node: Ident =>
          val indices = walk(node.idxs)
          doTransform(TreeCopier(node)(indices))
        case node: Sym =>
          val indices = walk(node.idxs)
          doTransform(TreeCopier(node)(indices))
        ////////////////////////////////////////////////////////////////////////
        // Decl
        ////////////////////////////////////////////////////////////////////////
        case node: Decl =>
          val ref = walk(node.ref)
          val desc = walk(node.desc)
          doTransform(TreeCopier(node)(ref, desc))
        ////////////////////////////////////////////////////////////////////////
        // Desc
        ////////////////////////////////////////////////////////////////////////
        case node: DescVar =>
          val spec = walk(node.spec)
          val initOpt = walk(node.initOpt)
          doTransform(TreeCopier(node)(spec, initOpt))
        case node: DescIn =>
          val spec = walk(node.spec)
          doTransform(TreeCopier(node)(spec))
        case node: DescOut =>
          val spec = walk(node.spec)
          val initOpt = walk(node.initOpt)
          doTransform(TreeCopier(node)(spec, initOpt))
        case node: DescPipeline =>
          val spec = walk(node.spec)
          doTransform(TreeCopier(node)(spec))
        case node: DescParam =>
          val spec = walk(node.spec)
          val initOpt = walk(node.initOpt)
          doTransform(TreeCopier(node)(spec, initOpt))
        case node: DescConst =>
          val spec = walk(node.spec)
          val init = walk(node.init)
          doTransform(TreeCopier(node)(spec, init))
        case node: DescGen =>
          val spec = walk(node.spec)
          val init = walk(node.init)
          doTransform(TreeCopier(node)(spec, init))
        case node: DescArray =>
          val elem = walk(node.elem)
          val size = walk(node.size)
          doTransform(TreeCopier(node)(elem, size))
        case node: DescSram =>
          val elem = walk(node.elem)
          val size = walk(node.size)
          doTransform(TreeCopier(node)(elem, size))
        case node: DescStack =>
          val elem = walk(node.elem)
          val size = walk(node.size)
          doTransform(TreeCopier(node)(elem, size))
        case node: DescType =>
          val spec = walk(node.spec)
          doTransform(TreeCopier(node)(spec))
        case node: DescEntity =>
          val body = walk(node.body)
          doTransform(TreeCopier(node)(body))
        case node: DescRecord =>
          val body = walk(node.body)
          doTransform(TreeCopier(node)(body))
        case node: DescInstance =>
          val spec = walk(node.spec)
          doTransform(TreeCopier(node)(spec))
        case node: DescSingleton =>
          val body = walk(node.body)
          doTransform(TreeCopier(node)(body))
        case node: DescFunc =>
          val ret = walk(node.ret)
          val args = walk(node.args)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(ret, args, body))
        case node: DescState =>
          val expr = walk(node.expr)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(expr, body))
        case node: DescChoice =>
          val choices = walk(node.choices)
          doTransform(TreeCopier(node)(choices))
        ////////////////////////////////////////////////////////////////////////
        // Gen
        ////////////////////////////////////////////////////////////////////////
        case node: GenIf =>
          val cond = walk(node.cond)
          val thenItems = walk(node.thenItems)
          val elseItems = walk(node.elseItems)
          doTransform(TreeCopier(node)(cond, thenItems, elseItems))
        case node: GenFor =>
          val decls = walk(node.decls)
          val cond = walk(node.cond)
          val step = walk(node.steps)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(decls, cond, step, body))
        case node: GenRange =>
          val decl = walk(node.decl)
          val end = walk(node.end)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(decl, end, body))
        ////////////////////////////////////////////////////////////////////////
        // Riz
        ////////////////////////////////////////////////////////////////////////
        case node: RizDecl =>
          val decl = walk(node.decl)
          doTransform(TreeCopier(node)(decl))
        ////////////////////////////////////////////////////////////////////////
        // Ent
        ////////////////////////////////////////////////////////////////////////
        case node: EntDecl =>
          val decl = walk(node.decl)
          doTransform(TreeCopier(node)(decl))
        case node: EntGen =>
          val gen = walk(node.gen)
          doTransform(TreeCopier(node)(gen))
        case node: EntConnect =>
          val lhs = walk(node.lhs)
          val rhs = walk(node.rhs)
          doTransform(TreeCopier(node)(lhs, rhs))
        case node: EntCombProcess =>
          val stmts = walk(node.stmts)
          doTransform(TreeCopier(node)(stmts))
        case node: EntVerbatim => doTransform(node)
        case node: EntComment  => doTransform(node)
        ////////////////////////////////////////////////////////////////////////
        // Rec
        ////////////////////////////////////////////////////////////////////////
        case node: RecDecl =>
          val decl = walk(node.decl)
          doTransform(TreeCopier(node)(decl))
        case node: RecGen =>
          val gen = walk(node.gen)
          doTransform(TreeCopier(node)(gen))
        case node: RecComment => doTransform(node)
        ////////////////////////////////////////////////////////////////////////
        // Stmt
        ////////////////////////////////////////////////////////////////////////
        case node: StmtDecl =>
          val decl = walk(node.decl)
          doTransform(TreeCopier(node)(decl))
        case node: StmtGen =>
          val gen = walk(node.gen)
          doTransform(TreeCopier(node)(gen))
        case node: StmtBlock =>
          val body = walk(node.body)
          doTransform(TreeCopier(node)(body))
        case node: StmtIf =>
          val cond = walk(node.cond)
          val thenStmts = walk(node.thenStmts)
          val elseStmts = walk(node.elseStmts)
          doTransform(TreeCopier(node)(cond, thenStmts, elseStmts))
        case node: StmtCase =>
          val expr = walk(node.expr)
          val cases = walk(node.cases)
          doTransform(TreeCopier(node)(expr, cases))
        case node: StmtLoop =>
          val body = walk(node.body)
          doTransform(TreeCopier(node)(body))
        case node: StmtWhile =>
          val cond = walk(node.cond)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(cond, body))
        case node: StmtFor =>
          val inits = walk(node.inits)
          val cond = walk(node.cond)
          val incr = walk(node.steps)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(inits, cond, incr, body))
        case node: StmtDo =>
          val cond = walk(node.cond)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(cond, body))
        case node: StmtLet =>
          val inits = walk(node.inits)
          val body = walk(node.body)
          doTransform(TreeCopier(node)(inits, body))
        case node: StmtFence    => doTransform(node)
        case node: StmtBreak    => doTransform(node)
        case node: StmtContinue => doTransform(node)
        case node: StmtGoto =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        case node: StmtReturn => doTransform(node)
        case node: StmtAssign =>
          val lhs = walk(node.lhs)
          val rhs = walk(node.rhs)
          doTransform(TreeCopier(node)(lhs, rhs))
        case node: StmtUpdate =>
          val lhs = walk(node.lhs)
          val rhs = walk(node.rhs)
          doTransform(TreeCopier(node)(lhs, rhs))
        case node: StmtPost =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        case node: StmtRead  => doTransform(node)
        case node: StmtWrite => doTransform(node)
        case node: StmtExpr =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        case node: StmtStall =>
          val cond = walk(node.cond)
          doTransform(TreeCopier(node)(cond))
        case node: StmtError   => doTransform(node)
        case node: StmtComment => doTransform(node)
        ////////////////////////////////////////////////////////////////////////
        // Case
        ////////////////////////////////////////////////////////////////////////
        case node: CaseGen =>
          val gen = walk(node.gen)
          doTransform(TreeCopier(node)(gen))
        case node: CaseRegular =>
          val cond = walk(node.cond)
          val stmts = walk(node.stmts)
          doTransform(TreeCopier(node)(cond, stmts))
        case node: CaseDefault =>
          val stmts = walk(node.stmts)
          doTransform(TreeCopier(node)(stmts))
        ////////////////////////////////////////////////////////////////////////
        // Expr
        ////////////////////////////////////////////////////////////////////////
        case node: ExprCall =>
          val expr = walk(node.expr)
          val args = walk(node.args)
          doTransform(TreeCopier(node)(expr, args))
        case node: ExprUnary =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        case node: ExprBinary =>
          val lhs = walk(node.lhs)
          val rhs = walk(node.rhs)
          doTransform(TreeCopier(node)(lhs, rhs))
        case node: ExprTernary =>
          val cond = walk(node.cond)
          val thenExpr = walk(node.thenExpr)
          val elseExpr = walk(node.elseExpr)
          doTransform(TreeCopier(node)(cond, thenExpr, elseExpr))
        case node: ExprRep =>
          val count = walk(node.count)
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(count, expr))
        case node: ExprCat =>
          val parts = walk(node.parts)
          doTransform(TreeCopier(node)(parts))
        case node: ExprIndex =>
          val expr = walk(node.expr)
          val index = walk(node.index)
          doTransform(TreeCopier(node)(expr, index))
        case node: ExprSlice =>
          val expr = walk(node.expr)
          val lidx = walk(node.lIdx)
          val ridx = walk(node.rIdx)
          doTransform(TreeCopier(node)(expr, lidx, ridx))
        case node: ExprSelect =>
          val expr = walk(node.expr)
          val idxs = walk(node.idxs)
          doTransform(TreeCopier(node)(expr, idxs))
        case node: ExprRef =>
          val ref = walk(node.ref)
          doTransform(TreeCopier(node)(ref))
        case node: ExprSym  => doTransform(node)
        case node: ExprType => doTransform(node)
        case node: ExprCast =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        case node: ExprInt   => doTransform(node)
        case node: ExprNum   => doTransform(node)
        case node: ExprStr   => doTransform(node)
        case node: ExprError => doTransform(node)
        ////////////////////////////////////////////////////////////////////////
        // Arg
        ////////////////////////////////////////////////////////////////////////
        case node: ArgP =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        case node: ArgN =>
          val expr = walk(node.expr)
          doTransform(TreeCopier(node)(expr))
        ////////////////////////////////////////////////////////////////////////
        // Thicket
        ////////////////////////////////////////////////////////////////////////
        case node: Thicket =>
          val trees = walk(node.trees)
          doTransform(TreeCopier(node)(trees))
      }
    }

    pushEntity foreach { _ =>
      entityStack.pop()
    }

    result
  }

  //////////////////////////////////////////////////////////////////////////////
  // Default checks to run after each pass
  //////////////////////////////////////////////////////////////////////////////

  val checkRefs = true
  val checkDefs = true

  override def defaultCheck(orig: Tree, tree: Tree): Unit = {
    assert(entityStack.isEmpty, this.getClass.getName + " " + entityStack)
    // TODO: Add back referencing checks
  }
}
