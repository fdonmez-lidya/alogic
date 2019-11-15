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
import com.argondesign.alogic.core.Symbols.Symbol

trait DescEntityOps { this: DescEntity =>

  final override lazy val decls: List[Decl] = body collect { case EntDecl(decl: Decl) => decl }

  final override lazy val params: List[Decl] = body collect {
    case EntDecl(decl @ Decl(_, _: DescParam)) => decl
  }

  final lazy val entities: List[Decl] = body collect {
    case EntDecl(decl @ Decl(_, _: DescEntity)) => decl
  }

  final lazy val instances: List[Decl] = body collect {
    case EntDecl(decl @ Decl(_, _: DescInstance)) => decl
  }

  final lazy val functions: List[Decl] = body collect {
    case EntDecl(decl @ Decl(_, _: DescFunc)) => decl
  }

  final lazy val states: List[Decl] = body collect {
    case EntDecl(decl @ Decl(_, _: DescState)) => decl
  }

  final lazy val connects: List[EntConnect] = body collect { case node: EntConnect => node }

  final lazy val combProcesses: List[EntCombProcess] = body collect {
    case node: EntCombProcess => node
  }

  final lazy val verbatims: List[EntVerbatim] = body collect { case node: EntVerbatim => node }

  final lazy val publicSymbols: List[Symbol] = decls collect {
    case Decl(Sym(symbol, _), _: DescIn)  => symbol
    case Decl(Sym(symbol, _), _: DescOut) => symbol
  }

}
