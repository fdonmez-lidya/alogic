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
// Lift nested entities, wire through directly accessed ports
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeReady
import com.argondesign.alogic.core.StorageTypes.StorageTypeDefault
import com.argondesign.alogic.core.Symbols._
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.mutable

final class LiftEntities(implicit cc: CompilerContext) extends TreeTransformer {

  // TODO: Only works for single nesting
  // TODO: Rewrite without collectAll

  // ports and consts declared in outer entities
  private val outerIPortSymbols = mutable.Stack[Set[Symbol]]()
  private val outerOPortSymbols = mutable.Stack[Set[Symbol]]()
  private val outerConstSymbols = mutable.Stack[Set[Symbol]]()

  // new ports that need to be created to connect up to directly accessed outer port
  private val freshIPortSymbols = mutable.Stack[mutable.LinkedHashMap[Symbol, Symbol]]()
  private val freshOPortSymbols = mutable.Stack[mutable.LinkedHashMap[Symbol, Symbol]]()
  // new consts that need to be created, together with their initializer expressions
  private val freshConstSymbols = mutable.Stack[mutable.LinkedHashMap[Symbol, (Symbol, Expr)]]()

  // new ports that need to be connected in this entity
  private val freshIConnSymbols = mutable.Stack[mutable.LinkedHashSet[(Symbol, Symbol)]]()
  private val freshOConnSymbols = mutable.Stack[mutable.LinkedHashSet[(Symbol, Symbol)]]()

  // Output ports with storage that have been pushed into nested entities need
  // to loose their storage and turn into wire ports, we collect these in a set
  private val stripStorageSymbols = mutable.Set[Symbol]()

  // Output slices are pushed into the referencing entity. We keep track of
  // referencing entities, and error if there is more than one, as this would
  // result in multiple slice instances driving the output ports.
  // TODO: This could be relaxed by allowing more than one nested entities to
  // reference an outer port so long as there is only one doing a .write or
  // assignment. The rest could have the referenced signals wired through to
  // them.
  private val outerORefs = mutable.Map[String, Symbol]()

  // Similarly to output slices, it is also invalid to reference an input
  // port with sync ready flow control from more than one nested entities, so
  // we keep track of those as well
  private val outerIRefs = mutable.Map[String, Symbol]()

  private var entityLevel = 0

  override def skip(tree: Tree): Boolean = tree match {
    // Skip root entities without any nested entities
    case desc: DescEntity => entityLevel == 0 && desc.entities.isEmpty
    // Skip any other root level definitions
    case desc: Desc => entityLevel == 0
    case _          => false
  }

  override def enter(tree: Tree): Unit = tree match {
    case Decl(Sym(symbol, _), desc: DescEntity) =>
      entityLevel += 1

      //////////////////////////////////////////////////////////////////////////
      // Collect outer ports and consts we are referencing
      //////////////////////////////////////////////////////////////////////////

      lazy val referencedSymbols = List from {
        desc collectAll { case ExprSym(symbol) => symbol }
      }

      val newIPortSymbols = if (outerIPortSymbols.isEmpty) {
        Nil
      } else {
        for {
          outerSymbol <- referencedSymbols
          if outerIPortSymbols.toList.exists(_ contains outerSymbol)
        } yield {
          outerSymbol -> cc.newSymbolLike(outerSymbol)
        }
      }
      freshIPortSymbols.push(mutable.LinkedHashMap(newIPortSymbols: _*))

      val newOPortSymbols = if (outerOPortSymbols.isEmpty) {
        Nil
      } else {
        for {
          outerSymbol <- referencedSymbols
          if outerOPortSymbols.toList.exists(_ contains outerSymbol)
        } yield {
          outerSymbol -> cc.newSymbolLike(outerSymbol)
        }
      }
      freshOPortSymbols.push(mutable.LinkedHashMap(newOPortSymbols: _*))

      val newConstSymbols = if (outerConstSymbols.isEmpty) {
        Nil
      } else {
        // Find all referenced constants
        val referenced = for {
          outerSymbol <- referencedSymbols
          if outerConstSymbols.toList.exists(_ contains outerSymbol)
        } yield {
          outerSymbol
        }

        // Recursively find all constants used in initializers of referenced constants
        @tailrec
        def loop(prev: List[Symbol], curr: List[Symbol]): List[Symbol] = {
          if (prev == curr) {
            curr
          } else {
            val referenced = curr flatMap { outerSymbol =>
              outerSymbol.init.get collect {
                case ExprSym(s) if outerConstSymbols.toList.exists(_ contains s) => s
              }
            }
            loop(curr, (curr ::: referenced).distinct)
          }
        }

        // Sort the symbols in source order and create new symbols
        loop(Nil, referenced) sortBy { _.loc.start } map { outerSymbol =>
          val innerSymbol = cc.newSymbolLike(outerSymbol)
          val init = outerSymbol.init.get
          // Make a temporary decl to assign the initializer
          innerSymbol.decl(init) regularize init.loc
          (outerSymbol, (innerSymbol, init))
        }
      }
      freshConstSymbols.push(mutable.LinkedHashMap(newConstSymbols: _*))

      //////////////////////////////////////////////////////////////////////////
      // Mark output ports to strip storage from
      //////////////////////////////////////////////////////////////////////////

      for ((outerSymbol, _) <- newOPortSymbols) {
        stripStorageSymbols add outerSymbol
      }

      //////////////////////////////////////////////////////////////////////////
      // Record references
      //////////////////////////////////////////////////////////////////////////

      for ((outerSymbol, _) <- newOPortSymbols) {
        outerORefs(symbol.name) = outerSymbol
      }

      for ((outerSymbol, _) <- newIPortSymbols) {
        outerSymbol.kind match {
          case TypeIn(_, FlowControlTypeReady) => outerIRefs(symbol.name) = outerSymbol
          case _                               =>
        }
      }

      //////////////////////////////////////////////////////////////////////////
      // Push ports and consts declared by us
      //////////////////////////////////////////////////////////////////////////

      val newISymbols = Set from {
        desc.decls.iterator collect { case Decl(Sym(s, _), _: DescIn) => s }
      }
      outerIPortSymbols.push(newISymbols)

      val newOSymbols = Set from {
        desc.decls.iterator collect { case Decl(Sym(s, _), _: DescOut) => s }
      }
      outerOPortSymbols.push(newOSymbols)

      val newCSymbols = Set from {
        desc.decls.iterator collect { case Decl(Sym(s, _), _: DescConst) => s }
      }
      outerConstSymbols.push(newCSymbols)

      //////////////////////////////////////////////////////////////////////////
      // Push placeholder empty map for fresh connections
      //////////////////////////////////////////////////////////////////////////
      freshIConnSymbols.push(mutable.LinkedHashSet())
      freshOConnSymbols.push(mutable.LinkedHashSet())

    case _ =>
  }

  def finishEntity(decl: Decl): List[Decl] =
    decl pipe {
      case decl @ Decl(_, desc: DescEntity) =>
        ////////////////////////////////////////////////////////////////////////
        // Create declarations for fresh ports
        ////////////////////////////////////////////////////////////////////////
        if (freshIPortSymbols.top.isEmpty && freshOPortSymbols.top.isEmpty) {
          decl
        } else {
          val freshIPortDecls = for (symbol <- freshIPortSymbols.top.valuesIterator) yield {
            EntDecl(symbol.decl) regularize symbol.loc
          }
          val freshOPortDecls = for (symbol <- freshOPortSymbols.top.valuesIterator) yield {
            EntDecl(symbol.decl) regularize symbol.loc
          }

          val newBody = List.from(freshIPortDecls ++ freshOPortDecls ++ desc.body)
          val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
          TypeAssigner(decl.copy(desc = newDesc) withLoc decl.loc)
        }
      case _ => unreachable
    } pipe {
      case decl @ Decl(_, desc: DescEntity) =>
        ////////////////////////////////////////////////////////////////////////
        // Create declarations for fresh consts
        ////////////////////////////////////////////////////////////////////////
        if (freshConstSymbols.top.isEmpty) {
          decl
        } else {
          val freshConstDecls = for ((symbol, init) <- freshConstSymbols.top.valuesIterator) yield {
            // Similar to above, but also walk the initializer to replace
            // references to outer constants
            val initializer = walk(init).asInstanceOf[Expr]
            EntDecl(Decl(Sym(symbol, Nil), symbol.kind.desc(initializer))) regularize symbol.loc
          }

          val newBody = List.from(freshConstDecls ++ desc.body)
          val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
          TypeAssigner(decl.copy(desc = newDesc) withLoc decl.loc)
        }
      case _ => unreachable
    } pipe {
      case decl @ Decl(_, desc: DescEntity) =>
        ////////////////////////////////////////////////////////////////////////
        // Strip storage from output ports where needed
        ////////////////////////////////////////////////////////////////////////
        if (stripStorageSymbols.isEmpty) {
          decl
        } else {
          val newBody = desc.body map {
            case e @ EntDecl(d @ Decl(Sym(s, _), desc @ DescOut(_, _, st, _)))
                if st != StorageTypeDefault && (stripStorageSymbols contains s) =>
              val newDesc = TypeAssigner(desc.copy(st = StorageTypeDefault) withLoc desc.loc)
              val newDecl = TypeAssigner(d.copy(desc = newDesc) withLoc d.loc)
              TypeAssigner(EntDecl(newDecl) withLoc e.loc)
            case other => other
          }
          val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
          TypeAssigner(decl.copy(desc = newDesc) withLoc decl.loc)
        }
      case _ => unreachable
    } pipe {
      case decl @ Decl(_, desc: DescEntity) =>
        ////////////////////////////////////////////////////////////////////////
        // Connect fresh inner ports to outer port
        ////////////////////////////////////////////////////////////////////////
        if (freshIConnSymbols.top.isEmpty && freshOConnSymbols.top.isEmpty) {
          decl
        } else {
          def instanceSymbolsOfType(eSymbol: Symbol): List[Symbol] = desc.instances collect {
            case Decl(Sym(iSymbol, _), DescInstance(ExprSym(`eSymbol`))) => iSymbol
          }

          val freshIConns = for {
            (srcPortSymbol, dstEntitySymbol) <- freshIConnSymbols.top.iterator
            dstInstanceSymbol <- instanceSymbolsOfType(dstEntitySymbol)
          } yield {
            val lhs = ExprSym(srcPortSymbol)
            val rhs = ExprSelect(ExprSym(dstInstanceSymbol), srcPortSymbol.name, Nil)
            EntConnect(lhs, List(rhs)) regularize decl.loc
          }

          val freshOConns = for {
            (srcEntitySymbol, dstPortSymbol) <- freshOConnSymbols.top.iterator
            srcInstanceSymbol <- instanceSymbolsOfType(srcEntitySymbol)
          } yield {
            val lhs = ExprSelect(ExprSym(srcInstanceSymbol), dstPortSymbol.name, Nil)
            val rhs = ExprSym(dstPortSymbol)
            EntConnect(lhs, List(rhs)) regularize decl.loc
          }

          val newBody = List.from(desc.body.iterator ++ freshIConns ++ freshOConns)
          val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
          TypeAssigner(decl.copy(desc = newDesc) withLoc decl.loc)
        }
      case _ => unreachable
    } pipe {
      case decl @ Decl(_, desc: DescEntity) =>
        ////////////////////////////////////////////////////////////////////////
        // Extract the nested entities to the same level as the parent entity
        ////////////////////////////////////////////////////////////////////////
        if (desc.entities.isEmpty) {
          decl :: Nil
        } else {
          val children = desc.entities
          val parent = {
            val newBody = desc.body filter {
              case EntDecl(Decl(_, _: DescEntity)) => false
              case _                               => true
            }
            val newDesc = TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)
            TypeAssigner(decl.copy(desc = newDesc) withLoc decl.loc)
          }

          val parentName = decl.symbol.name

          // Prefix child names with parent name
          children foreach { child =>
            child.symbol.name = parentName + cc.sep + child.symbol.name
          }

          parent :: children
        }
      case _ => unreachable
    } tap { _ =>
      freshIConnSymbols.pop()
      freshOConnSymbols.pop()
      freshConstSymbols.pop()

      // Add ports created in this entity to connections required in the outer entity
      if (freshIConnSymbols.nonEmpty) {
        for ((iPortSymbol, _) <- freshIPortSymbols.top) {
          freshIConnSymbols.top.add((iPortSymbol, decl.symbol))
        }
      }

      if (freshOConnSymbols.nonEmpty) {
        for ((oPortSymbol, _) <- freshOPortSymbols.top) {
          freshOConnSymbols.top.add((decl.symbol, oPortSymbol))
        }
      }

      freshIPortSymbols.pop()
      freshOPortSymbols.pop()
      outerIPortSymbols.pop()
      outerOPortSymbols.pop()
      outerConstSymbols.pop()

      entityLevel -= 1

      if (entityLevel == 0) {
        for ((oSymbol, group) <- outerORefs.groupBy { _._2 } if group.size > 1) {
          val first =
            s"Output port '${oSymbol.name}' is referenced by more than one nested entities:"
          cc.error(oSymbol.loc, first :: group.keys.toList: _*)
        }

        for ((iSymbol, group) <- outerIRefs.groupBy { _._2 } if group.size > 1) {
          val first =
            s"Input port '${iSymbol.name}' with 'sync ready' flow control is referenced by more than one nested entities:"
          cc.error(iSymbol.loc, first :: group.keys.toList: _*)
        }
      }
    }

  override def transform(tree: Tree): Tree = tree match {
    case decl @ Decl(_, _: DescEntity) if entityLevel == 1 =>
      val results = finishEntity(decl)
      TypeAssigner(Thicket(results) withLoc decl.loc)

    case EntDecl(decl @ Decl(_, _: DescEntity)) =>
      val results = finishEntity(decl) map { entity =>
        TypeAssigner(EntDecl(entity) withLoc entity.loc)
      }
      TypeAssigner(Thicket(results) withLoc tree.loc)

    // Re-type references to entities as their ports might have changed
    case node @ ExprSym(symbol) if symbol.kind.isType && symbol.kind.asType.kind.isEntity =>
      TypeAssigner(node.copy() withLoc node.loc)

    // Rewrite references to outer ports as references to the newly created inner ports
    case ExprSym(symbol) => {
      freshIPortSymbols.top.get(symbol) orElse
        freshOPortSymbols.top.get(symbol) map { innerSymbol =>
        ExprSym(innerSymbol) regularize tree.loc
      }
    } orElse {
      freshConstSymbols.top.get(symbol) map {
        case (innerSymbol, _) => ExprSym(innerSymbol) regularize tree.loc
      }
    } getOrElse tree

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    assert(outerIPortSymbols.isEmpty)
    assert(outerOPortSymbols.isEmpty)
    assert(outerConstSymbols.isEmpty)
    assert(freshIPortSymbols.isEmpty)
    assert(freshOPortSymbols.isEmpty)
    assert(freshConstSymbols.isEmpty)
    assert(freshIConnSymbols.isEmpty)
    assert(freshOConnSymbols.isEmpty)

    tree visit {
      case node: DescEntity if node.entities.nonEmpty =>
        cc.ice(node, s"Nested entities remain after LiftEntities")
    }
  }

}

object LiftEntities extends TreeTransformerPass {
  val name = "lift-entities"
  def create(implicit cc: CompilerContext) = new LiftEntities
}
