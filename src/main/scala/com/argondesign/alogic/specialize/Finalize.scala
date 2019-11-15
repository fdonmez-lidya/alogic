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
// Finalize specialization of entity
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.specialize

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable

private[specialize] object Finalize {

  // Type all constants and simplify initializers (this also type checks the
  // final parameter assignments). Rename according to actual parameters.
  def apply(decl: Decl)(implicit cc: CompilerContext): Option[Decl] = {
    require(!decl.desc.isParametrized)

    val nameComponents = mutable.ListBuffer[String](decl.symbol.name)

    var hadError = false

    val transform: TreeTransformer = new TreeTransformer {
      override val typed = false
      override val checkRefs = false

      def typeCheck(tree: Tree*): Boolean =
        tree forall { cc.typeCheck(_) contains true } tap { hadError |= !_ }

      var level = 0

      override def skip(tree: Tree): Boolean = tree match {
        case decl @ Decl(_, _: DescConst) => !typeCheck(decl)
        case _: DescConst                 => false
        case _                            => level == 2
      }

      override def enter(tree: Tree): Unit = tree match {
        case _: Decl => level += 1
        case _       =>
      }

      override def transform(tree: Tree): Tree = tree match {
        // Simplify constants
        case desc @ DescConst(_, init) =>
          val newInit = init.simplify
          if (newInit ne init) {
            desc.copy(init = newInit) withLoc desc.loc
          } else {
            tree
          }

        // Gather parameter assignments
        case Decl(Sym(symbol, _), _) =>
          level -= 1
          if (symbol.attr.wasParam.isSet && level == 1) {
            // Add name component
            symbol.init.get.value match {
              case Some(v) => nameComponents append s"${symbol.name}_$v"
              case None    => unreachable // Parameter values are known by now
            }
            // Reduce noise
            symbol.attr.wasParam.clear()
          }
          tree

        //
        case _ => tree
      }
    }

    var result: Decl = decl

    result = (decl rewrite transform).asInstanceOf[Decl]

    // Rename based on actual parameter values
    result.symbol.name = nameComponents mkString cc.sep

    if (hadError) None else Some(result)
  }
}
