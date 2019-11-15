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
// Checks for unused variables
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.util.unreachable

import scala.collection.mutable

final class UnusedCheck(postElaborate: Boolean)(implicit cc: CompilerContext)
    extends TreeTransformer {

  override val typed = false

  // Set of declared symbols, keyed by entity containing the definition
  private val declared =
    mutable.Map[Option[Symbol], mutable.Set[Symbol]](None -> mutable.Set())

  // Set of referenced symbols, keyed by entity containing the reference
  private val used =
    mutable.Map[Option[Symbol], mutable.Set[Symbol]](None -> mutable.Set())

  // Set of symbols which contain external references
  private val hasExtRefs = mutable.Set[Symbol]()

  // Node counter
  private var count = 0

  // Root node file name
  private var rootFileName: String = _

  // Declaration symbol stack
  private val symbolStack = mutable.Stack[Symbol]()

  // Flag to indicate we are in a verbatim entity
  private var inVerbatimEntity = false

  private def markDecl(symbol: Symbol): Unit = declared(symbolStack.headOption) add symbol

  private def markUsed(symbol: Symbol): Unit = used(symbolStack.headOption) add symbol

  private def checkExtRef(symbol: Symbol): Unit = {
    // Only need to do this if we haven't found an external reference yet.
    if (!(symbolStack.headOption exists hasExtRefs)) {
      val keys = (symbolStack.iterator.drop(1) map { Some(_) }) ++ Iterator.single(None)
      if (keys map declared exists { _ contains symbol }) {
        symbolStack.headOption foreach hasExtRefs.add
      }
    }
  }

  private def processEntity(symbol: Symbol, variant: EntityVariant.Type, body: List[Ent]): Unit = {
    // Mark the root entity as used
    if (symbolStack.isEmpty) {
      markUsed(symbol)
    }
    declared(Some(symbol)) = mutable.Set()
    used(Some(symbol)) = mutable.Set()
    symbolStack push symbol
    inVerbatimEntity = variant == EntityVariant.Ver
    // Mark declarations up front so nested entities can check external refs
    body foreach {
      case EntDecl(Decl(Sym(s, _), _)) => markDecl(s)
      case _                           =>
    }
  }

  override def enter(tree: Tree): Unit = {
    if (count == 0) {
      rootFileName = tree.loc.source.name
    }
    count += 1
    tree match {
      case ExprSym(symbol) =>
        // Mark symbol as used
        markUsed(symbol)
        // Check if this is an external reference
        checkExtRef(symbol)

      case ExprRef(Sym(symbol, _)) =>
        // Mark symbol as used
        markUsed(symbol)
        // Check if this is an external reference
        checkExtRef(symbol)

      case Decl(Sym(symbol, _), desc) =>
        // Add symbol
        markDecl(symbol)
        // Mark all verbatim declarations as used
        if (inVerbatimEntity) {
          markUsed(symbol)
        }
        // Mark externally defined types as used
        if (symbol.loc.file != rootFileName) {
          markUsed(symbol)
        }
        // After specializations, mark root symbols as used
        if (postElaborate && symbolStack.isEmpty) {
          markUsed(symbol)
        }
        // Behaviour specific to certain kinds of definitions
        desc match {
          case DescEntity(variant, body) =>
            processEntity(symbol, variant, body)
          case DescSingleton(variant, body) =>
            processEntity(symbol, variant, body)
          case record: DescRecord =>
            // Mark all members as used
            record.decls foreach { decl =>
              markUsed(decl.symbol)
            }
          case _: DescFunc =>
            // Mark entry point functions as used
            if (symbol.attr.entry contains true) {
              markUsed(symbol)
            }
          case _: DescChoice =>
            // Assume used
            markUsed(symbol)
          case _ =>
        }

      case GenRange(Decl(Sym(symbol, _), _), _, _, _) =>
        // Mark loop variable as used
        markUsed(symbol)

      case _ =>
    }
  }

  override def transform(tree: Tree): Tree = {
    count -= 1

    tree match {
      case Decl(_, _: DescEntity) =>
        symbolStack.pop()
        inVerbatimEntity = false
      case Decl(Sym(symbol, _), _: DescSingleton) =>
        symbolStack.pop()
        inVerbatimEntity = false
        // Mark this instance as used if it has external references
        if (hasExtRefs(symbol)) {
          markUsed(symbol)
        }
      case Decl(Sym(symbol, _), _: DescInstance) =>
        if (!postElaborate) {
          // We don't know the type of this yet, assume used
          markUsed(symbol)
        } else {
          // Mark this instance as used if it has external references
          symbol.kind match {
            case TypeType(TypeEntity(s, _)) if hasExtRefs(s) => markUsed(symbol)
            case TypeUnknown                                 => markUsed(symbol)
            case _                                           =>
          }
        }
      case _ =>
    }

    // When we have processed the root node, check references
    if (count == 0) {
      val allDeclared = declared.values.foldLeft(Set.empty[Symbol]) { _ union _ }

      val allUsed = used.values.foldLeft(Set.empty[Symbol]) { _ union _ }

      for {
        symbol <- allDeclared diff allUsed
        if (!postElaborate || !symbol.kind.isConst) && !(symbol.attr.unused.get contains true)
      } {
        val hint = symbol.decl.desc match {
          case _: DescVar       => "Variable"
          case _: DescIn        => "Input port"
          case _: DescOut       => "Output port"
          case _: DescPipeline  => "Pipeline variable"
          case _: DescParam     => "Parameter"
          case _: DescConst     => "Constant"
          case _: DescGen       => "'gen' variable"
          case _: DescArray     => "Array"
          case _: DescSram      => "SRAM"
          case _: DescType      => "Type"
          case _: DescEntity    => "Entity"
          case _: DescRecord    => "struct"
          case _: DescInstance  => "Instance"
          case _: DescSingleton => "Singleton instance"
          case _: DescFunc      => "Function"
          case _                => unreachable
        }
        val name = symbol.attr.sourceName.get match {
          case None               => symbol.name
          case Some((base, idxs)) => idxs mkString (s"$base#[", ", ", "]")
        }
        cc.warning(symbol, s"$hint '$name' is unused")
      }
    }

    // Nothing to actually rewrite
    tree
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(count == 0)
    assert(symbolStack.isEmpty)
    assert(!inVerbatimEntity)
  }
}

object UnusedCheck {
  def apply(postElaborate: Boolean): Pass = {
    new TreeTransformerPass {
      val name = "unused-check"
      def create(implicit cc: CompilerContext) = new UnusedCheck(postElaborate)
    }
  }
}
