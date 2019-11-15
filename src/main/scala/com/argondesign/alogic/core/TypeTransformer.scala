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
// A Type transformer used to modify Types
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.core

import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.lib.TreeLikeTransformer

// Type transformers are applied during a post-order traversal of a Type.
abstract class TypeTransformer(implicit cc: CompilerContext) extends TreeLikeTransformer[Type] {

  ///////////////////////////////////////////////////////////////////////////////
  // Internals
  ///////////////////////////////////////////////////////////////////////////////

  protected final override def walk(tree: Type): Type = {
    if (skip(tree)) {
      tree
    } else {
      enter(tree)
      tree match {
        case node: TypeSInt => transform(node)
        case node: TypeUInt => transform(node)
        case node: TypeNum  => transform(node)
        case node: TypeVector =>
          val elementType = walk(node.elementType)
          transform(TypeCopier(node)(elementType))
        case TypeVoid         => transform(TypeVoid)
        case TypeStr          => transform(TypeStr)
        case node: TypeEntity => transform(node)
        case node: TypeRecord => transform(node)
        case node: TypeIn =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeOut =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypePipeline =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeParam =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeConst =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeGen =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeArray =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeSram =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeStack =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeType =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeNone =>
          val kind = walk(node.kind)
          transform(TypeCopier(node)(kind))
        case node: TypeParametrized => transform(node)
        case TypeCombStmt           => transform(TypeCombStmt)
        case TypeCtrlStmt           => transform(TypeCtrlStmt)
        case node: TypeCombFunc =>
          val argTypes = walk(node.argTypes)
          val retType = walk(node.retType)
          transform(TypeCopier(node)(argTypes, retType))
        case node: TypeCtrlFunc =>
          val argTypes = walk(node.argTypes)
          val retType = walk(node.retType)
          transform(TypeCopier(node)(argTypes, retType))
        case node: TypePolyFunc => transform(node)
        case TypeUnknown        => transform(TypeUnknown)
        case node: TypeChoice   => transform(node)
        case TypeState          => transform(TypeState)
        case TypeMisc           => transform(TypeMisc)
        case TypeError          => transform(TypeError)
      }
    }
  }
}
