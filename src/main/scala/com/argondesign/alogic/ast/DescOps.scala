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
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.ast.Trees._

trait DescOps { this: Desc =>

  def decls: List[Decl] = Nil

  def params: List[Decl] = Nil

  final lazy val isParametrized: Boolean = params.nonEmpty

  final lazy val initializer: Option[Expr] = this match {
    case DescVar(_, iOpt)       => iOpt
    case DescOut(_, _, _, iOpt) => iOpt
    case DescParam(_, iOpt)     => iOpt
    case DescConst(_, i)        => Some(i)
    case DescGen(_, i)          => Some(i)
    case _                      => None
  }

}
