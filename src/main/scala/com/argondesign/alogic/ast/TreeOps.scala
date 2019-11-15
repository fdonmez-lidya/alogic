////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2017-2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Common members of ast.Trees.Tree
// These are factored out into a separate file to keep ast.Trees readable
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.antlr.AlogicParser._
import com.argondesign.alogic.antlr._
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.frontend.Parser.Parseable
import com.argondesign.alogic.passes.AddCasts
import com.argondesign.alogic.passes.ReplaceUnaryTicks
import com.argondesign.alogic.passes.ResolvePolyFunc
import com.argondesign.alogic.transform.Regularize
import com.argondesign.alogic.util.unreachable

import scala.language.implicitConversions

trait TreeOps extends TreePrintOps { this: Tree =>

  //////////////////////////////////////////////////////////////////////////////
  // Trees nodes have a type 'tpe' which can be set once
  //////////////////////////////////////////////////////////////////////////////

  final private[this] var _tpe: Type = null

  final def hasTpe: Boolean = _tpe != null

  final def tpe: Type = if (hasTpe) _tpe else unreachable

  final def tpeOpt: Option[Type] = Option(_tpe)

  final def withTpe(kind: Type): this.type = {
    if (hasTpe) {
      unreachable
    } else {
      _tpe = kind
    }
    this
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Rewrite with TreeTransformer
  ////////////////////////////////////////////////////////////////////////////////

  final def rewrite(tt: TreeTransformer): Tree = tt(this)

  ////////////////////////////////////////////////////////////////////////////
  // Regularize the tree
  ////////////////////////////////////////////////////////////////////////////

  def regularize(loc: Loc)(implicit cc: CompilerContext): this.type = {
    this rewrite new Regularize(loc)
    this
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Pretty print
  ////////////////////////////////////////////////////////////////////////////////

  def toPrettyString: String = {
    val sb = new StringBuilder
    var lvl = 0
    for (c <- this.toString) {
      sb append c
      c match {
        case '(' =>
          lvl += 1
          sb append ("\n" + "  " * lvl)
        case ')' =>
          lvl -= 1
        case ',' =>
          sb append ("\n" + "  " * lvl)
        case _ =>
      }
    }
    sb.toString
  }
}

//////////////////////////////////////////////////////////////////////////////
// Polymorphic extension methods on Trees
//////////////////////////////////////////////////////////////////////////////

final class TreeExt[T <: Tree](val tree: T) extends AnyVal {

  ////////////////////////////////////////////////////////////////////////////////
  // Bring tree into a normal form that can be directly evaluated
  ////////////////////////////////////////////////////////////////////////////////

  def normalize(implicit cc: CompilerContext): T = {
    val res = tree rewrite {
      new ReplaceUnaryTicks
    } rewrite {
      new ResolvePolyFunc
    } rewrite {
      new AddCasts
    }
    res.asInstanceOf[T]
  }
}

trait ObjectTreeOps {

  //////////////////////////////////////////////////////////////////////////////
  // Implicit dispatchers for any Tree that can be directly parsed by the parser
  //////////////////////////////////////////////////////////////////////////////

  implicit final val parseableRoot: Parseable[Root] = new Parseable[Root] {
    type C = RootContext
    def parse(parser: AlogicParser): RootContext = parser.root()
    def build(ctx: RootContext)(implicit cc: CompilerContext): Root = RootBuilder(ctx)
  }

  implicit final val parseableDecl: Parseable[Decl] = new Parseable[Decl] {
    type C = DeclContext
    def parse(parser: AlogicParser): DeclContext = parser.decl()
    def build(ctx: DeclContext)(implicit cc: CompilerContext): Decl = DeclBuilder(ctx)
  }

  implicit final val parseableRiz: Parseable[Riz] = new Parseable[Riz] {
    type C = RizContext
    def parse(parser: AlogicParser): RizContext = parser.riz()
    def build(ctx: RizContext)(implicit cc: CompilerContext): Riz = RizBuilder(ctx)
  }

  implicit final val parseableEnt: Parseable[Ent] = new Parseable[Ent] {
    type C = EntContext
    def parse(parser: AlogicParser): EntContext = parser.ent()
    def build(ctx: EntContext)(implicit cc: CompilerContext): Ent = EntBuilder(ctx)
  }

  implicit final val parseableRec: Parseable[Rec] = new Parseable[Rec] {
    type C = RecContext
    def parse(parser: AlogicParser): RecContext = parser.rec()
    def build(ctx: RecContext)(implicit cc: CompilerContext): Rec = RecBuilder(ctx)
  }

  implicit final val parseableGen: Parseable[Gen] = new Parseable[Gen] {
    type C = GenContext
    def parse(parser: AlogicParser): GenContext = parser.gen()
    def build(ctx: GenContext)(implicit cc: CompilerContext): Gen = GenBuilder(ctx)
  }

  implicit final val parseableStmt: Parseable[Stmt] = new Parseable[Stmt] {
    type C = StmtContext
    def parse(parser: AlogicParser): StmtContext = parser.stmt()
    def build(ctx: StmtContext)(implicit cc: CompilerContext): Stmt = StmtBuilder(ctx)
  }

  implicit final val parseableExpr: Parseable[Expr] = new Parseable[Expr] {
    type C = ExprContext
    def parse(parser: AlogicParser): ExprContext = parser.expr()
    def build(ctx: ExprContext)(implicit cc: CompilerContext): Expr = ExprBuilder(ctx)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Tree to TreeExt implicit conversion
  //////////////////////////////////////////////////////////////////////////////

  implicit def tree2TreeExt[T <: Tree](tree: T): TreeExt[T] = new TreeExt[T](tree)
}
