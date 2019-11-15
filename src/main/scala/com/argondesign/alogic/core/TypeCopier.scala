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
// A copy on write Type copier used in type transformations
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.core

import Types._

// scalastyle:off token

// Given a Type and new child nodes, create new Type if children are not the same as
// the children of the current Type, otherwise reuse existing Type. Note that only
// fields containing Type instances are checked as other fields are not transformed
// recursively in TypeTransformer
object TypeCopier {

  def apply(tree: TypeVector)(elementType: Type): TypeVector = {
    if (elementType eq tree.elementType) tree else TypeVector(elementType, tree.size)
  }

  def apply(tree: TypeIn)(kind: Type): TypeIn = {
    if (kind eq tree.kind) tree else TypeIn(kind.asFund, tree.fc)
  }

  def apply(tree: TypeOut)(kind: Type): TypeOut = {
    if (kind eq tree.kind) tree else TypeOut(kind.asFund, tree.fc, tree.st)
  }

  def apply(tree: TypePipeline)(kind: Type): TypePipeline = {
    if (kind eq tree.kind) tree else TypePipeline(kind.asFund)
  }

  def apply(tree: TypeParam)(kind: Type): TypeParam = {
    if (kind eq tree.kind) tree else TypeParam(kind.asFund)
  }

  def apply(tree: TypeConst)(kind: Type): TypeConst = {
    if (kind eq tree.kind) tree else TypeConst(kind.asFund)
  }

  def apply(tree: TypeGen)(kind: Type): TypeGen = {
    if (kind eq tree.kind) tree else TypeGen(kind.asFund)
  }

  def apply(tree: TypeArray)(kind: Type): TypeArray = {
    if (kind eq tree.kind) tree else TypeArray(kind.asFund, tree.size)
  }

  def apply(tree: TypeSram)(kind: Type): TypeSram = {
    if (kind eq tree.kind) tree else TypeSram(kind.asFund, tree.size, tree.st)
  }

  def apply(tree: TypeStack)(kind: Type): TypeStack = {
    if (kind eq tree.kind) tree else TypeStack(kind.asFund, tree.size)
  }

  def apply(tree: TypeType)(kind: Type): TypeType = {
    if (kind eq tree.kind) tree else TypeType(kind.asFund)
  }

  def apply(tree: TypeNone)(kind: Type): TypeNone = {
    if (kind eq tree.kind) tree else TypeNone(kind.asFund)
  }

  def apply(tree: TypeCombFunc)(argTypes: List[Type], retType: Type): TypeCombFunc = {
    if ((argTypes eq tree.argTypes) && (retType eq tree.retType)) {
      tree
    } else {
      assert(argTypes forall { _.isFund })
      tree.copy(retType = retType.asFund, argTypes = argTypes.asInstanceOf[List[TypeFund]])
    }
  }

  def apply(tree: TypeCtrlFunc)(argTypes: List[Type], retType: Type): TypeCtrlFunc = {
    if ((argTypes eq tree.argTypes) && (retType eq tree.retType)) {
      tree
    } else {
      assert(argTypes forall { _.isFund })
      tree.copy(retType = retType.asFund, argTypes = argTypes.asInstanceOf[List[TypeFund]])
    }
  }

}
