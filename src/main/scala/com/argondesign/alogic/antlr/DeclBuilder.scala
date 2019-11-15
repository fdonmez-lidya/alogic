////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2018-2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Geza Lore
//
// DESCRIPTION:
//
// Build a Decl AST from an Antlr4 parse tree
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.antlr

import com.argondesign.alogic.antlr.AlogicParser._
import com.argondesign.alogic.antlr.AntlrConverters._
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes._
import com.argondesign.alogic.core.FuncVariant
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.enums.EntityVariant
import com.argondesign.alogic.util.unreachable

import scala.jdk.CollectionConverters._
import scala.util.ChainingSyntax

object DeclBuilder extends BaseBuilder[DeclContext, Decl] with ChainingSyntax {

  private def attributes(ctx: AttrsContext)(implicit cc: CompilerContext): Map[String, Expr] =
    Map from {
      for (attr <- ctx.attr.iterator.asScala) yield {
        val key = attr.IDENTIFIER.text
        val value = if (attr.expr != null) {
          ExprBuilder(attr.expr)
        } else {
          Expr(1) withLoc ctx.loc
        }
        key -> value
      }
    }

  def apply(ctx: DeclContext)(implicit cc: CompilerContext): Decl = {
    object FCTVisitor extends AlogicScalarVisitor[FlowControlType] {
      override def defaultResult: FlowControlType =
        FlowControlTypeNone
      override def visitFCTSync(ctx: FCTSyncContext): FlowControlType =
        FlowControlTypeValid
      override def visitFCTSyncReady(ctx: FCTSyncReadyContext): FlowControlType =
        FlowControlTypeReady
      override def visitFCTSyncAccept(ctx: FCTSyncAcceptContext): FlowControlType =
        FlowControlTypeAccept
    }

    object STTVisitor extends AlogicScalarVisitor[StorageType] {
      override def defaultResult: StorageType =
        StorageTypeDefault
      override def visitSTTWire(ctx: STTWireContext): StorageType =
        StorageTypeWire
      override def visitSTTSlices(ctx: STTSlicesContext): StorageType = {
        val kinds = ctx.slices.asScala.toList map {
          _.text match {
            case "bubble" => StorageSliceBub
            case "fslice" => StorageSliceFwd
            case "bslice" => StorageSliceBwd
            case _        => unreachable
          }
        }
        StorageTypeSlices(kinds)
      }
    }

    object Visitor extends AlogicScalarVisitor[Decl] {
      //////////////////////////////////////////////////////////////////////////
      // Attach attributes
      //////////////////////////////////////////////////////////////////////////

      override def visitDecl(ctx: DeclContext): Decl =
        if (ctx.attrs != null) {
          visit(ctx.declbase) tap { _.ref.asInstanceOf[Ident].attr addAll attributes(ctx.attrs) }
        } else {
          visit(ctx.declbase)
        }

      //////////////////////////////////////////////////////////////////////////
      // Decl
      //////////////////////////////////////////////////////////////////////////

      private def decl(ctx: DeclbaseContext, ident: Ident, desc: Desc) = {
        val loc = ctx.loc.copy(point = ident.loc.start)
        desc withLoc loc
        Decl(ident, desc) withLoc loc
      }

      override def visitDeclVar(ctx: DeclVarContext): Decl = {
        val spec = ExprBuilder(ctx.expr(0))
        val initOpt = if (ctx.init != null) Some(ExprBuilder(ctx.init)) else None
        decl(ctx, IdentBuilder(ctx.ident), DescVar(spec, initOpt))
      }

      override def visitDeclIn(ctx: DeclInContext): Decl = {
        val spec = ExprBuilder(ctx.expr)
        val fct = FCTVisitor(ctx.fct)
        decl(ctx, IdentBuilder(ctx.ident), DescIn(spec, fct))
      }

      override def visitDeclOut(ctx: DeclOutContext): Decl = {
        val spec = ExprBuilder(ctx.expr(0))
        val fct = FCTVisitor(ctx.fct)
        val stt = STTVisitor(ctx.stt)
        val initOpt = if (ctx.init != null) Some(ExprBuilder(ctx.init)) else None
        decl(ctx, IdentBuilder(ctx.ident), DescOut(spec, fct, stt, initOpt))
      }

      override def visitDeclPipeline(ctx: DeclPipelineContext): Decl = {
        val spec = ExprBuilder(ctx.expr)
        decl(ctx, IdentBuilder(ctx.ident), DescPipeline(spec))
      }

      override def visitDeclParam(ctx: DeclParamContext): Decl = {
        val spec = ExprBuilder(ctx.expr(0))
        val initOpt = if (ctx.init != null) Some(ExprBuilder(ctx.init)) else None
        decl(ctx, IdentBuilder(ctx.IDENTIFIER), DescParam(spec, initOpt))
      }

      override def visitDeclConst(ctx: DeclConstContext): Decl = {
        val spec = ExprBuilder(ctx.expr(0))
        val init = ExprBuilder(ctx.expr(1))
        decl(ctx, IdentBuilder(ctx.IDENTIFIER), DescConst(spec, init))
      }

      override def visitDeclArr(ctx: DeclArrContext): Decl = {
        val elem = ExprBuilder(ctx.expr(0))
        val size = ExprBuilder(ctx.expr(1))
        decl(ctx, IdentBuilder(ctx.ident), DescArray(elem, size))
      }

      override def visitDeclSram(ctx: DeclSramContext): Decl = {
        val elem = ExprBuilder(ctx.expr(0))
        val size = ExprBuilder(ctx.expr(1))
        val stt = if (ctx.wire != null) StorageTypeWire else StorageTypeReg
        decl(ctx, IdentBuilder(ctx.ident), DescSram(elem, size, stt))
      }

      override def visitDeclType(ctx: DeclTypeContext): Decl = {
        val spec = ExprBuilder(ctx.expr)
        decl(ctx, IdentBuilder(ctx.ident), DescType(spec))
      }

      override def visitDeclEntity(ctx: DeclEntityContext): Decl = {
        val variant = ctx.entity_keyword.text match {
          case "fsm"     => EntityVariant.Fsm
          case "network" => EntityVariant.Net
          case _         => EntityVariant.Ver
        }
        val body = EntBuilder(ctx.ent)
        decl(ctx, IdentBuilder(ctx.ident), DescEntity(variant, body))
      }

      override def visitDeclRecord(ctx: DeclRecordContext): Decl = {
        val body = RecBuilder(ctx.rec)
        decl(ctx, IdentBuilder(ctx.ident), DescRecord(body))
      }

      override def visitDeclInstance(ctx: DeclInstanceContext): Decl = {
        val spec = ExprBuilder(ctx.expr)
        decl(ctx, IdentBuilder(ctx.ident), DescInstance(spec))
      }

      override def visitDeclSingleton(ctx: DeclSingletonContext): Decl = {
        val variant = ctx.entity_keyword.text match {
          case "fsm"     => EntityVariant.Fsm
          case "network" => EntityVariant.Net
          case _         => EntityVariant.Ver
        }
        val body = EntBuilder(ctx.ent)
        decl(ctx, IdentBuilder(ctx.ident), DescSingleton(variant, body))
      }

      override def visitDeclFunc(ctx: DeclFuncContext): Decl = {
        val ret = ExprBuilder(ctx.expr)
        val body = StmtBuilder(ctx.stmt)
        decl(ctx, IdentBuilder(ctx.ident), DescFunc(FuncVariant.None, ret, Nil, body))
      }
    }

    Visitor(ctx)
  }

}
