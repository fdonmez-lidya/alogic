////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2017-2018 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Peter de Rivaz/Geza Lore
//
// DESCRIPTION:
//
// Pretty printers for Tree nodes
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.ast

import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.FlowControlTypes._
import com.argondesign.alogic.core.StorageTypes._
import com.argondesign.alogic.core.enums.EntityVariant

import scala.util.chaining._

trait TreePrintOps extends { this: Tree =>

  def toSource(implicit cc: CompilerContext): String = v(this)(cc, 0)

  private final def block(
      header: String,
      body: List[Tree]
  )(
      implicit cc: CompilerContext,
      indent: Int
  ): String = {
    if (body.isEmpty) {
      s"$header {}"
    } else {
      val i = "  " * indent
      s"""|$header {
          |$i  ${body map { v(_)(cc, indent + 1) } mkString s"\n$i  "}
          |$i}""".stripMargin
    }
  }

  private final def v(fct: FlowControlType): String = fct match {
    case FlowControlTypeNone   => ""
    case FlowControlTypeValid  => "sync "
    case FlowControlTypeReady  => "sync ready "
    case FlowControlTypeAccept => "sync accept "
  }

  private final def v(st: StorageType): String = st match {
    case StorageTypeDefault => ""
    case StorageTypeReg     => "reg "
    case StorageTypeWire    => "wire "
    case StorageTypeSlices(slices) =>
      slices map {
        case StorageSliceFwd => "fslice"
        case StorageSliceBwd => "bslice"
        case StorageSliceBub => "bubble"
      } mkString ("", " ", " ")
  }

  private final def v(ev: EntityVariant.Type): String = ev match {
    case EntityVariant.Fsm => "fsm"
    case EntityVariant.Net => "network"
    case EntityVariant.Ver => "verbatim entity"
  }

  private final def vs(
      trees: List[Tree],
      sep: String
  )(
      implicit cc: CompilerContext,
      indent: Int
  ): String = trees map v mkString s", "

  private final def vs(
      trees: List[Tree],
      start: String,
      sep: String,
      end: String
  )(
      implicit cc: CompilerContext,
      indent: Int
  ): String = trees map v mkString (start, sep, end)

  private final def vo(treeOpt: Option[Tree])(implicit cc: CompilerContext, indent: Int): String =
    treeOpt map v getOrElse ""

  private final def v(tree: Tree)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case node: Root    => v(node)
    case node: Ref     => v(node)
    case node: Decl    => v(node)
    case node: Desc    => v(node, "_")
    case node: Gen     => v(node)
    case node: Riz     => v(node)
    case node: Ent     => v(node)
    case node: Rec     => v(node)
    case node: Stmt    => v(node)
    case node: Case    => v(node)
    case node: Expr    => v(node)
    case node: Arg     => v(node)
    case node: Thicket => v(node)
  }

  private final def v(tree: Root)(implicit cc: CompilerContext, indent: Int): String = {
    block("root", tree.decls)
  }

  private final def v(ref: Ref)(implicit cc: CompilerContext, indent: Int): String = ref match {
    case Ident(name, Nil)     => name
    case Sym(symbol, Nil)     => s"${symbol.name}@${symbol.id}"
    case Ident(name, indices) => vs(indices, s"$name#[", ",", "]")
    case Sym(symbol, indices) => vs(indices, s"${symbol.name}@${symbol.id}#[", ",", "]")
  }

  private final def v(tree: Decl)(implicit cc: CompilerContext, indent: Int): String = {
    val attr = tree.ref pipe {
      case Sym(symbol, _)                     => symbol.attr.toSource
      case ident: Ident if ident.attr.isEmpty => ""
      case ident: Ident =>
        ident.attr.iterator map { case (k, v) => s"$k = $v" } mkString ("(* ", ", ", " *)")
    } pipe {
      case ""  => ""
      case str => str + "\n" + "  " * indent
    }

    val name = v(tree.ref)

    attr + v(tree.desc, name)
  }

  // format: off
  private final def v(tree: Desc, name: String)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case DescVar(spec, None)                => s"${v(spec)} $name"
    case DescVar(spec, Some(init))          => s"${v(spec)} $name = ${v(init)}"
    case DescIn(spec, fct)                  => s"in ${v(fct)}${v(spec)} $name"
    case DescOut(spec, fct, st, None)       => s"out ${v(fct)}${v(st)}${v(spec)} $name"
    case DescOut(spec, fct, st, Some(init)) => s"out ${v(fct)}${v(st)}${v(spec)} $name = ${v(init)}"
    case DescPipeline(spec)                 => s"pipeline ${v(spec)} $name"
    case DescParam(spec, None)              => s"param ${v(spec)} $name"
    case DescParam(spec, Some(init))        => s"param ${v(spec)} $name = ${v(init)}"
    case DescConst(spec, init)              => s"const ${v(spec)} $name = ${v(init)}"
    case DescGen(spec, init)                => s"gen ${v(spec)} $name = ${v(init)}"
    case DescArray(elem, size)              => s"${v(elem)} $name[$size]"
    case DescSram(elem, size, st)           => s"sram ${v(st)}${v(elem)} $name[$size]"
    case DescStack(elem, size)              => s"stack ${v(elem)} $name[$size]"
    case DescType(spec)                     => s"typedef ${v(spec)} $name"
    case DescEntity(variant, body)          => block(s"${v(variant)} $name", body)
    case DescRecord(body)                   => block(s"record $name", body)
    case DescInstance(spec)                 => s"$name = new ${v(spec)}"
    case DescSingleton(variant, body)       => block(s"new ${v(variant)} $name", body)
    case DescFunc(_, ret, args, body)       => block(s"${v(ret)} $name(${vs(args, ", ")})", body)
    case DescState(expr, body)              => block(s"state $name ${v(expr)}", body)
    case DescChoice(choices) => vs(choices, "choice<", ",", "> ") + name
  }
  // format: on

  // format: off
  private final def v(tree: Gen)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case GenIf(cond, thenItems, Nil)       => block(s"gen if (${v(cond)}) ", thenItems)
    case GenIf(cond, thenItems, elseItems) => block(s"gen if (${v(cond)}) ", thenItems) + block(s" else", elseItems)
    case GenFor(inits, cond, steps, body)  => block(s"gen for (${vs(inits, ", ")}; ${v(cond)} ; ${vs(steps, ", ")})", body)
    case GenRange(decl, op, end, body)     => block(s"gen for (${v(decl)} $op ${v(end)})", body)
  }
  // format: on

  private final def v(tree: Riz)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case RizDecl(decl) => s"${v(decl)}"
  }

  private final def v(tree: Ent)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case EntDecl(decl)           => s"${v(decl)}"
    case EntGen(gen)             => v(gen)
    case EntConnect(lhs, rhs)    => s"${v(lhs)} -> ${vs(rhs, ", ")};"
    case EntCombProcess(stmts)   => block("always", stmts)
    case EntVerbatim(lang, body) => s"verbatim $lang {$body}"
    case EntComment(str)         => "//" + str
  }

  private final def v(tree: Rec)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case RecDecl(decl)   => s"${v(decl)}"
    case RecGen(gen)     => v(gen)
    case RecComment(str) => "//" + str
  }

  // format: off
  private final def v(tree: Stmt)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case StmtDecl(decl)                    => s"${v(decl)}"
    case StmtGen(gen)                      => v(gen)
    case StmtBlock(body)                   => block("", body)
    case StmtIf(cond, ts, Nil)             => block(s"if (${v(cond)})", ts)
    case StmtIf(cond, ts, es)              => block(s"if (${v(cond)})", ts) + block(s" else", es)
    case StmtCase(expr, cases)             => block(s"case (${v(expr)})", cases)
    case StmtLoop(body)                    => block("loop", body)
    case StmtWhile(cond, body)             => block(s"while (${v(cond)})", body)
    case StmtFor(inits, cond, steps, body) => block(s"for (${vs(inits, ",")} ; ${vo(cond)} ; ${vs(steps, ", ")})", body)
    case StmtDo(cond, body)                => block(s"do", body) + s" while (${v(cond)});"
    case StmtLet(inits, body)              => block(s"let (${vs(inits, ", ")})", body)
    case StmtFence()                       => "fence;"
    case StmtBreak()                       => "break;"
    case StmtContinue()                    => "continue;"
    case StmtGoto(expr)                    => s"goto ${v(expr)};"
    case StmtReturn()                      => "return;"
    case StmtAssign(lhs, rhs)              => s"${v(lhs)} = ${v(rhs)};"
    case StmtUpdate(lhs, op, rhs)          => s"${v(lhs)} $op= ${v(rhs)};"
    case StmtPost(expr, op)                => s"${v(expr)}$op;"
    case StmtExpr(expr)                    => s"${v(expr)};"
    case StmtRead()                        => "read;"
    case StmtWrite()                       => "write;"
    case StmtComment(str)                  => "//" + str
    case StmtStall(cond)                   => s"stall ${v(cond)};"
    case StmtError()                       => "/* Error statement */"
  }
  // format: on

  private final def v(tree: Case)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case CaseGen(gen)             => v(gen)
    case CaseRegular(cond, stmts) => block(s"${vs(cond, ", ")} :", stmts)
    case CaseDefault(stmts)       => block("default :", stmts)
  }

  // format: off
  private final def v(tree: Expr)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case ExprCall(expr, args)                  => s"${v(expr)}(${vs(args, ", ")})"
    case ExprUnary(op, expr)                   => s"$op${v(expr)}"
    case ExprBinary(lhs, op, rhs)              => s"${v(lhs)} $op ${v(rhs)}"
    case ExprTernary(cond, thenExpr, elseExpr) => s"${v(cond)} ? ${v(thenExpr)} : ${v(elseExpr)}"
    case ExprRep(count, expr)                  => s"{${v(count)}{${v(expr)}}}"
    case ExprCat(parts)                        => s"{${vs(parts, ", ")}}"
    case ExprIndex(expr, index)                => s"${v(expr)}[${v(index)}]"
    case ExprSlice(expr, lIdx, op, rIdx)       => s"${v(expr)}[${v(lIdx)}$op${v(rIdx)}]"
    case ExprSelect(expr, selector, Nil)       => s"${v(expr)}.$selector"
    case ExprSelect(expr, selector, idxs)      => s"${v(expr)}.$selector#[${vs(idxs, ", ")}]"
    case ExprRef(ref)                          => v(ref)
//    case ExprSym(symbol)                       => s"${symbol.name}@${symbol.id}"
    case ExprSym(symbol)                       => symbol.name
    case ExprType(kind)                        => s"${kind.toSource}"
    case ExprCast(kind, expr)                  => s"(${kind.toSource})(${v(expr)})"
    case ExprInt(true, width, value)           => s"$width'sd$value"
    case ExprInt(false, width, value)          => s"$width'd$value"
    case ExprNum(true, value)                  => s"'sd$value"
    case ExprNum(false, value)                 => s"$value"
    case ExprStr(value)                        => s""""$value""""
    case ExprError()                           => "ExprError"
  }
  // format: on

  private final def v(tree: Arg)(implicit cc: CompilerContext, indent: Int): String = tree match {
    case ArgP(expr)       => v(expr)
    case ArgN(name, expr) => s"$name = ${v(expr)}"
  }

  private final def v(tree: Thicket)(implicit cc: CompilerContext, indent: Int): String = {
    block("thicket", tree.trees)
  }

}
