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
// Convert StorageTypeDefault to the appropriate concrete value
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes._
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.typer.TypeAssigner

import scala.collection.mutable

final class DefaultStorage(implicit cc: CompilerContext) extends TreeTransformer {

  // Set of output ports accessed through port methods or directly
  private[this] val accessedSet = mutable.Set[Symbol]()

  // Set of output ports connected with '->'
  private[this] val connectedSet = mutable.Set[Symbol]()

  private[this] var inConnect = false

  private[this] var entityVariant: EntityVariant.Type = _

  override def enter(tree: Tree): Unit = tree match {
    case DescEntity(variant, _) =>
      entityVariant = variant

    case _: EntConnect =>
      assert(!inConnect)
      inConnect = true

    case ExprSym(symbol) if symbol.kind.isOut =>
      if (inConnect) {
        connectedSet add symbol
      } else {
        accessedSet add symbol
      }

    case _ =>
  }

  override def transform(tree: Tree): Tree = tree match {
    case _: EntConnect =>
      assert(inConnect)
      inConnect = false
      tree

    // Update types or all output declarations that use the default storage type
    case decl @ Decl(_, desc: DescEntity) =>
      val newBody = desc.body map {
        case ent @ EntDecl(d @ Decl(Sym(symbol, Nil), s @ DescOut(_, fc, StorageTypeDefault, _))) =>
          // Compute the appropriate default storage type
          val newSt = if (entityVariant == EntityVariant.Ver) {
            StorageTypeWire
          } else if (connectedSet contains symbol) {
            StorageTypeWire
          } else if (accessedSet contains symbol) {
            fc match {
              case FlowControlTypeReady  => StorageTypeSlices(List(StorageSliceFwd))
              case FlowControlTypeAccept => StorageTypeWire
              case _                     => StorageTypeReg
            }
          } else {
            StorageTypeWire
          }
          val newS = TypeAssigner(s.copy(st = newSt) withLoc s.loc)
          val newD = TypeAssigner(d.copy(desc = newS) withLoc d.loc)
          TypeAssigner(EntDecl(newD) withLoc ent.loc)
        case ent => ent
      }
      val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
      TypeAssigner(decl.copy(desc = newDesc) withLoc decl.loc)

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(!inConnect)
    tree visitAll {
      case node @ DescOut(_, _, StorageTypeDefault, _) =>
        cc.ice(node, "Default storage type remains")
    }
  }
}

object DefaultStorage extends TreeTransformerPass {
  val name = "default-storage"
  def create(implicit cc: CompilerContext) = new DefaultStorage
}
