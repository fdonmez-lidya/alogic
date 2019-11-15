////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Any pass relying on Tree.id may fail with structural sharing. This pass
// copies any shared nodes.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable

final class RemoveStructuralSharing(implicit cc: CompilerContext) extends TreeTransformer {

  // Set of stack symbols to replace
  private val visited = mutable.Set[Int]()

  override def transform(tree: Tree): Tree = {
    if (!(visited contains tree.id)) {
      visited add tree.id
      tree
    } else {
      val duplicate = tree match {
        case node: Root => node.copy()

        case node: Ident => node.copy()
        case node: Sym   => node.copy()

        case node: Decl => node.copy()

        case node: DescVar       => node.copy()
        case node: DescIn        => node.copy()
        case node: DescOut       => node.copy()
        case node: DescPipeline  => node.copy()
        case node: DescParam     => node.copy()
        case node: DescConst     => node.copy()
        case node: DescGen       => node.copy()
        case node: DescArray     => node.copy()
        case node: DescSram      => node.copy()
        case node: DescStack     => node.copy()
        case node: DescType      => node.copy()
        case node: DescEntity    => node.copy()
        case node: DescRecord    => node.copy()
        case node: DescInstance  => node.copy()
        case node: DescSingleton => node.copy()
        case node: DescFunc      => node.copy()
        case node: DescState     => node.copy()
        case node: DescChoice    => node.copy()

        case node: GenIf    => node.copy()
        case node: GenFor   => node.copy()
        case node: GenRange => node.copy()

        case node: RizDecl => node.copy()

        case node: EntDecl        => node.copy()
        case node: EntGen         => node.copy()
        case node: EntConnect     => node.copy()
        case node: EntCombProcess => node.copy()
        case node: EntVerbatim    => node.copy()
        case node: EntComment     => node.copy()

        case node: RecDecl    => node.copy()
        case node: RecGen     => node.copy()
        case node: RecComment => node.copy()

        case node: StmtDecl    => node.copy()
        case node: StmtGen     => node.copy()
        case node: StmtBlock   => node.copy()
        case node: StmtIf      => node.copy()
        case node: StmtCase    => node.copy()
        case node: StmtLoop    => node.copy()
        case node: StmtWhile   => node.copy()
        case node: StmtFor     => node.copy()
        case node: StmtDo      => node.copy()
        case node: StmtLet     => node.copy()
        case _: StmtFence      => StmtFence()
        case _: StmtBreak      => StmtBreak()
        case _: StmtContinue   => StmtContinue()
        case node: StmtGoto    => node.copy()
        case _: StmtReturn     => StmtReturn()
        case node: StmtAssign  => node.copy()
        case node: StmtUpdate  => node.copy()
        case node: StmtPost    => node.copy()
        case _: StmtRead       => StmtRead()
        case _: StmtWrite      => StmtWrite()
        case node: StmtExpr    => node.copy()
        case node: StmtStall   => node.copy()
        case _: StmtError      => StmtError()
        case node: StmtComment => node.copy()

        case node: CaseGen     => node.copy()
        case node: CaseRegular => node.copy()
        case node: CaseDefault => node.copy()

        case node: ExprCall    => node.copy()
        case node: ExprUnary   => node.copy()
        case node: ExprBinary  => node.copy()
        case node: ExprTernary => node.copy()
        case node: ExprRep     => node.copy()
        case node: ExprCat     => node.copy()
        case node: ExprIndex   => node.copy()
        case node: ExprSlice   => node.copy()
        case node: ExprSelect  => node.copy()
        case node: ExprRef     => node.copy()
        case node: ExprSym     => node.copy()
        case node: ExprType    => node.copy()
        case node: ExprCast    => node.copy()
        case node: ExprInt     => node.copy()
        case node: ExprNum     => node.copy()
        case node: ExprStr     => node.copy()
        case _: ExprError      => ExprError()

        case node: ArgP => node.copy()
        case node: ArgN => node.copy()

        case _: Thicket => unreachable
      }
      duplicate withLoc tree.loc withTpe tree.tpe
    }
  }
}

object RemoveStructuralSharing extends TreeTransformerPass {
  val name = "remove-structural-sharing"
  def create(implicit cc: CompilerContext) = new RemoveStructuralSharing
}
