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
// Transform parameters of definition to constants using given bindings
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.specialize

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext

private[specialize] object Substitute {

  // Substitute top level parameters given the bindings and convert them to
  // constants. Unbound parameters will be converted using their default
  // initializers if exists. If an unbound parameter with no default initializer
  // exist, returns Left(list of unbound parameter decls). Otherwise returns
  // Right((substituted tree, unused bindings)).
  def apply(
      decl: Decl,
      bindings: Map[String, Expr]
  )(implicit cc: CompilerContext): Either[List[Decl], (Decl, Map[String, Expr])] = {
    require(decl.ref.asInstanceOf[Sym].idxs.isEmpty)
    if (!decl.desc.isParametrized) {
      // If there are none, we are done
      Right((decl, bindings))
    } else {
      // Otherwise gather the parameter definitions
      val paramDecls: List[Decl] = decl.desc.params

      // Find the unbound parameters with no default initializers
      val unboundDecls = paramDecls filter { d =>
        d.desc.initializer.isEmpty && !(bindings contains d.name)
      }

      if (unboundDecls.nonEmpty) {
        // Stop if unbound parameters exits and return their decls
        Left(unboundDecls)
      } else {
        // Otherwise do the real work of substituting the parameters

        // Clone all defined symbols to ensure independence from the input
        // but not yet clone the symbol in the decl itself.
        val symbolMap = Map from {
          decl collectAll {
            case Decl(Sym(symbol, _), _) if symbol != decl.symbol => symbol -> symbol.dup
          }
        }

        // Compute the bindings for the cloned symbols, using the default
        // initializer if no explicit binding is provided.
        val paramBindings = Map from {
          paramDecls map { paramDecl =>
            val symbol = paramDecl.symbol
            val newSymbol = symbolMap(symbol)
            newSymbol.attr.wasParam set true
            newSymbol -> bindings.getOrElse(symbol.name, paramDecl.desc.initializer.get)
          }
        }

        // Transform that replaces the bound parameters
        val transform = new TreeTransformer {
          override val typed: Boolean = false
          override val checkRefs: Boolean = false

          override def transform(tree: Tree): Tree = tree match {
            // Clone the symbol in the input decl itself last
            case Sym(symbol, _) if symbol == decl.symbol =>
              Sym(symbol.dup, Nil) withLoc tree.loc

            // Replace cloned symbols
            case node: Sym =>
              symbolMap.get(node.symbol) match {
                case Some(symbol) => node.copy(symbol = symbol) withLoc node.loc
                case none         => tree
              }
            case node: ExprSym =>
              symbolMap.get(node.symbol) match {
                case Some(symbol) => node.copy(symbol = symbol) withLoc node.loc
                case none         => tree
              }

            // Change bound (outermost decl) parameters into constants
            case decl @ Decl(Sym(symbol, _), desc @ DescParam(spec, _)) =>
              paramBindings.get(symbol) match {
                case None => tree // Not inside outermost decl
                case Some(init) =>
                  val newDesc = DescConst(spec, init) withLoc desc.loc
                  decl.copy(desc = newDesc) withLoc decl.loc
              }

            // Other
            case _ => tree
          }
        }

        // Perform the transform
        val substituted = (decl rewrite transform).asInstanceOf[Decl] ensuring {
          !_.desc.isParametrized
        }

        // Compute the unused bindings
        val unusedBindings = bindings filterNot {
          case (name, _) => paramBindings exists { _._1.name == name }
        }

        // Done
        Right((substituted, unusedBindings))
      }
    }
  }
}
