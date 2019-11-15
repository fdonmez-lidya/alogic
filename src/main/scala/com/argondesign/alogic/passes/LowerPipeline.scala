////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2017 - 2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Peter de Rivaz/Geza Lore
//
// DESCRIPTION:
//
// Transform pipeline variables and read/write statements into pipeline ports
// and .read()/.write() on those ports.
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.ast.TreeTransformer
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes.FlowControlTypeReady
import com.argondesign.alogic.core.Loc
import com.argondesign.alogic.core.StorageTypes.StorageSliceFwd
import com.argondesign.alogic.core.StorageTypes.StorageTypeSlices
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types._
import com.argondesign.alogic.typer.TypeAssigner
import com.argondesign.alogic.util.unreachable

import scala.annotation.tailrec
import scala.collection.immutable.ListMap
import scala.collection.mutable
import scala.language.postfixOps

final class LowerPipeline(implicit cc: CompilerContext) extends TreeTransformer {

  // TODO: special case the empty pipe stage (with body 'read; write; fence;') to avoid packing
  // TODO: support in arbitrary context, not just plain single nesting

  // List of active pipeline symbols, for each stage
  private var actSetMap: Map[Symbol, Set[Symbol]] = _

  // Map to previous/next stage
  private var prevMap: Map[Symbol, Symbol] = _
  private var nextMap: Map[Symbol, Symbol] = _

  // Pipeline input and output port symbols for current stage
  private var iPortSymbolOpt: Option[Symbol] = None
  private var oPortSymbolOpt: Option[Symbol] = None

  // Pipelined variable symbols declared in this stage
  private var freshSymbols: ListMap[String, Symbol] = ListMap()

  // TODO: this was just a quick fix after redesigning the Decl/Desc
  // representations, do it in a less horrible way.
  val innerTransform: TreeTransformer = new TreeTransformer {
    override def transform(tree: Tree): Tree = tree match {
      // Transform the nested entity
      // TODO: mark inlined
      case desc: DescEntity => {

        // Construct pipeline port declarations
        val iPortOpt = iPortSymbolOpt map { symbol =>
          EntDecl(symbol.decl) regularize desc.loc
        }
        val oPortOpt = oPortSymbolOpt map { symbol =>
          EntDecl(symbol.decl) regularize desc.loc
        }

        // Construct declarations for pipeline variables
        val freshDecls = freshSymbols.values map { symbol =>
          EntDecl(symbol.decl) regularize desc.loc
        }

        val result = desc.copy(
          body = List.concat(iPortOpt, oPortOpt, freshDecls, desc.body)
        ) withLoc desc.loc

        TypeAssigner(result)
      }

      case node: StmtRead if iPortSymbolOpt.isEmpty => {
        cc.fatal(node, "'read' statement in first pipeline stage")
      }

      case node: StmtWrite if oPortSymbolOpt.isEmpty => {
        cc.fatal(node, "'write' statement in last pipeline stage")
      }

      // Rewrite 'read;' statement to '{....} = pipeline_i.read();'
      case node: StmtRead =>
        iPortSymbolOpt.get.kind match {
          case TypeIn(iPortKind: TypeRecord, _) =>
            val lhsRefs = iPortKind.publicSymbols map { symbol =>
              ExprSym(freshSymbols(symbol.name))
            }
            val lhs = ExprCat(lhsRefs)
            val rhs = ExprCall(ExprSelect(ExprSym(iPortSymbolOpt.get), "read", Nil), Nil)
            StmtAssign(lhs, rhs) regularize node.loc
          case _ => unreachable
        }

      // Rewrite 'write;' statement to 'pipeline_o.write({....});'
      case node: StmtWrite =>
        oPortSymbolOpt.get.kind match {
          case TypeOut(oPortKind: TypeRecord, _, _) =>
            val rhsRefs = oPortKind.publicSymbols map { symbol =>
              ExprSym(freshSymbols(symbol.name))
            }
            val arg = ArgP(ExprCat(rhsRefs))
            val call = ExprCall(ExprSelect(ExprSym(oPortSymbolOpt.get), "write", Nil), List(arg))
            StmtExpr(call) regularize node.loc
          case _ => unreachable
        }

      // Rewrite references to pipeline variables to references to the newly declared symbols
      // otherwise re-type references
      case node @ ExprSym(symbol) =>
        symbol.kind match {
          case _: TypePipeline => ExprSym(freshSymbols(symbol.name)) regularize node.loc
          case _               => TypeAssigner(node.copy() withLoc node.loc)
        }

      case _ => tree
    }
  }

  private var firstEntity = true

  val replacements = mutable.Map[Symbol, Decl]()

  override def skip(tree: Tree): Boolean = tree match {
    // If this is the root entity, skip it if it has no pipeline declarations
    case Decl(_, desc: DescEntity) if firstEntity =>
      firstEntity = false
      desc.decls forall { !_.symbol.kind.isPipeline }
    // Skip decls being replaced
    case decl: Decl => replacements contains decl.symbol
    // Skip if a replacement is available
    case _ => false
  }

  override def enter(tree: Tree): Unit = tree match {
    case outer: DescEntity =>
      // Work out the prev an next maps
      nextMap = outer.connects collect {
        case EntConnect(ExprSym(iSymbolA), List(ExprSym(iSymbolB))) =>
          (iSymbolA.kind, iSymbolB.kind) match {
            case (TypeEntity(eSymbolA, _), TypeEntity(eSymbolB, _)) => eSymbolA -> eSymbolB
            case _                                                  => unreachable
          }
      } toMap

      prevMap = nextMap map { _.swap }

      // Sort entities using pipeline connections
      val entities = {
        @tailrec
        def lt(a: Symbol, b: Symbol): Boolean = nextMap.get(a) match {
          case Some(`b`)   => true
          case Some(other) => lt(other, b)
          case None        => false
        }
        outer.entities sortWith {
          case (aEntity, bEntity) => lt(aEntity.symbol, bEntity.symbol)
        }
      }

      // Collect pipeline symbols used in nested entities
      val useSets = for {
        inner <- entities
      } yield {
        inner collect {
          case ExprSym(symbol) if symbol.kind.isInstanceOf[TypePipeline] => symbol
          case Sym(symbol, _) if symbol.kind.isInstanceOf[TypePipeline]  => symbol
        } toSet
      }

      // Propagate uses between first and last use to create activeSets
      actSetMap = {
        @tailrec
        def loop(useSets: List[Set[Symbol]], actSets: List[Set[Symbol]]): List[Set[Symbol]] = {
          if (useSets.isEmpty) {
            actSets.reverse
          } else {
            // symbols active at any stage later than the current stage
            val actTail = useSets.tail.foldLeft(Set.empty[Symbol]) { _ | _ }
            // symbols active at the previous stage
            val actPrev = actSets.head
            // symbols active at the current stage
            val actHead = useSets.head | (actTail & actPrev)
            // Do next stage
            loop(useSets.tail, actHead :: actSets)
          }
        }
        val propagated = loop(useSets.tail, List(useSets.head))
        (entities zip propagated) map { case (entity, actSet) => entity.symbol -> actSet } toMap
      }

      // Rewrite stages
      for (inner @ Decl(_, _: DescEntity) <- outer.entities) {
        // Figure out pipeline port types
        val actPrev = prevMap.get(inner.symbol) map { actSetMap(_) } getOrElse Set[Symbol]()
        val actCurr = actSetMap(inner.symbol)
        val actNext = nextMap.get(inner.symbol) map { actSetMap(_) } getOrElse Set[Symbol]()

        def makePortSymbol(in: Boolean, actSet: Set[Symbol]): Option[Symbol] = {
          if (actSet.isEmpty) {
            None
          } else {
            val aSymbols = actSet.toList sortWith { _.id < _.id }
            val mSymbols = aSymbols map { symbol =>
              cc.newSymbol(symbol.name, symbol.loc) tap { _.kind = symbol.kind.underlying }
            }
            val name = if (in) "pipeline_i" else "pipeline_o"
            val sSymbol = cc.newSymbol(s"${name}_t", Loc.synthetic)
            val struct = TypeType(TypeRecord(sSymbol, mSymbols))
            sSymbol.kind = struct
            val kind = if (in) {
              TypeIn(struct.kind, FlowControlTypeReady)
            } else {
              val st = StorageTypeSlices(List(StorageSliceFwd))
              TypeOut(struct.kind, FlowControlTypeReady, st)
            }
            Some(cc.newSymbol(name, inner.loc) tap { _.kind = kind })
          }
        }

        iPortSymbolOpt = makePortSymbol(in = true, actPrev & actCurr)
        oPortSymbolOpt = makePortSymbol(in = false, actNext & actCurr)

        freshSymbols = {
          val pairs = for (psymbol <- actCurr.toList sortWith { _.id < _.id }) yield {
            val name = psymbol.name
            val kind = psymbol.kind.underlying
            name -> (cc.newSymbol(name, inner.loc) tap { _.kind = kind })
          }
          ListMap(pairs: _*)
        }

        replacements(inner.symbol) = (inner rewrite innerTransform).asInstanceOf[Decl]
      }

      // re-type instances
      for (inst: Decl <- outer.instances) {
        replacements(inst.symbol) = (inst rewrite innerTransform).asInstanceOf[Decl]
      }

    case _ =>
  }

  override def transform(tree: Tree): Tree = tree match {
    // Transform the outer entity
    case desc: DescEntity =>
      val newBody = desc.body filter {
        // loose pipeline variable declarations
        case EntDecl(decl) => !decl.symbol.kind.isPipeline
        case _             => true
      } map {
        // replace nested definitions
        case ent: EntDecl =>
          replacements.get(ent.decl.symbol) match {
            case Some(decl) => TypeAssigner(EntDecl(decl) withLoc ent.loc)
            case None       => ent
          }
        // rewrite pipeline connections
        case conn @ EntConnect(lhs, List(rhs)) =>
          (lhs.tpe, rhs.tpe) match {
            // If its an instance -> instance connection, select the new pipeline ports
            case (_: TypeEntity, _: TypeEntity) =>
              val newLhs = ExprSelect(lhs, "pipeline_o", Nil) withLoc lhs.loc
              val newRhs = ExprSelect(rhs, "pipeline_i", Nil) withLoc rhs.loc
              val newConn = EntConnect(newLhs, List(newRhs))
              newConn regularize conn.loc
            // Otherwise leave it alone
            case _ => conn
          }
        //
        case other => other
      }

      TypeAssigner(desc.copy(body = newBody) withLoc desc.loc)

    // Re-type references
    case node: ExprSym => TypeAssigner(node.copy() withLoc node.loc)

    case _ => tree
  }

  override def finalCheck(tree: Tree): Unit = {
    tree visit {
      case node: StmtRead  => cc.ice(node, "read statement remains after LowerPipeline")
      case node: StmtWrite => cc.ice(node, "write statement remains after LowerPipeline")
      case node: Decl if node.symbol.kind.isPipeline =>
        cc.ice(node, "Pipeline variable declaration remains after LowerPipeline")
      case node @ ExprSym(symbol) =>
        symbol.kind match {
          case _: TypePipeline =>
            cc.ice(node, "Pipeline variable reference remains after LowerPipeline")
          case _ =>
        }
    }

    tree visitAll {
      case node: Tree if node.tpe.isPipeline =>
        cc.ice(node, "Pipeline variable type remains after LowerPipeline")
    }
  }

}

object LowerPipeline extends TreeTransformerPass {
  val name = "lower-pipeline"
  def create(implicit cc: CompilerContext) = new LowerPipeline
}
