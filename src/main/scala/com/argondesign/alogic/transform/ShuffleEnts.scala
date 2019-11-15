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
// Randomly shuffle order of List[Ent] in Trees (for testing purposes)
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.transform

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.typer.TypeAssigner

import scala.util.Random

final class ShuffleEnts(override val typed: Boolean, val seed: Int)(implicit cc: CompilerContext)
    extends TreeTransformer {
  override val checkRefs: Boolean = false

  private[this] def shuffle(name: String, ents: List[Ent]): List[Ent] = {
    val random = new Random(name.foldLeft(seed)(_ * _))
    random shuffle ents
  }

  override def transform(tree: Tree): Tree = tree match {
    case decl @ Decl(ref, desc: DescEntity) =>
      val newDesc = desc.copy(body = shuffle(ref.name, desc.body)) withLoc desc.loc
      val newDecl = decl.copy(desc = newDesc) withLoc decl.loc
      if (tree.hasTpe) {
        TypeAssigner(newDesc)
        TypeAssigner(newDecl)
      }
      newDecl
    case decl @ Decl(ref, desc: DescSingleton) =>
      val newDesc = desc.copy(body = shuffle(ref.name, desc.body)) withLoc desc.loc
      val newDecl = decl.copy(desc = newDesc) withLoc decl.loc
      if (tree.hasTpe) {
        TypeAssigner(newDesc)
        TypeAssigner(newDecl)
      }
      newDecl
    case _ =>
      tree
  }
}
