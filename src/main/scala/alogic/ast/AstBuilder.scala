////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2017 Argon Design Ltd. All rights reserved.
//
// Module : Scala Alogic Compiler
// Author : Peter de Rivaz/Geza Lore
//
// DESCRIPTION:
//
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
////////////////////////////////////////////////////////////////////////////////

package alogic.ast

import scala.collection.immutable.ListMap
import org.antlr.v4.runtime.ParserRuleContext
import alogic.Antlr4Conversions._
import alogic.Message
import alogic.VScalarVisitor
import alogic.antlr.VParser._

// The aim of the AstBuilder stage is:
//   Build an abstract syntax tree
//   Deal with as many error conditions as possible (while we can easily report error location)
//   Deal with typedefs
//   Deal with variable scope
//
// We use different visitors for the different things we wish to extract.

////////////////////////////////////////////////////////////////////////////////
// Visitors and data structures required when parsing all kinds of source files
////////////////////////////////////////////////////////////////////////////////
class CommonContext(root: ParserRuleContext, initialTypedefs: Map[String, Type]) {
  // Collect type definitions and entityContext
  val (typedefs, entityCtx) = root match {
    case ctx: StartContext     => ExtractTypedefs(ctx, initialTypedefs)
    case ctx: EntityFSMContext => (initialTypedefs, ctx)
  }

  // Build scopes and allocate static variable names
  private[this] val symtab = new Symtab(root, typedefs)

  val exprVisitor = new ExprVisitor(Some(symtab), typedefs)

  val lvalVisitor = new LValVisitor(Some(symtab), typedefs)

  val knownTypeVisitor = new KnownTypeVisitor(Some(symtab), typedefs)

  object LookUpDecl extends VScalarVisitor[Decl] {
    override def visitTaskDeclOut(ctx: TaskDeclOutContext) = symtab(ctx)
    override def visitTaskDeclIn(ctx: TaskDeclInContext) = symtab(ctx)
    override def visitTaskDeclConst(ctx: TaskDeclConstContext) = symtab(ctx)
    override def visitTaskDeclPipeline(ctx: TaskDeclPipelineContext) = symtab(ctx)
    override def visitTaskDeclParam(ctx: TaskDeclParamContext) = symtab(ctx)
    override def visitTaskDeclVerilog(ctx: TaskDeclVerilogContext) = symtab(ctx)
    override def visitTaskDecl(ctx: TaskDeclContext) = visit(ctx.decl)
    override def visitDeclVarNoInit(ctx: DeclVarNoInitContext) = symtab(ctx)
    override def visitDeclVarInit(ctx: DeclVarInitContext) = symtab(ctx)
    override def visitDeclArr(ctx: DeclArrContext) = symtab(ctx)
  }

  object VerilogFunctionVisitor extends VScalarVisitor[VerilogFunction] {
    override def visitVerilogFunction(ctx: VerilogFunctionContext) = VerilogFunction(Attr(ctx.loc), ctx.VERILOGBODY.text.drop(1).dropRight(1))
  }
}

////////////////////////////////////////////////////////////////////////////////
// Builder to handle 'fsm' task definitions
////////////////////////////////////////////////////////////////////////////////
class FsmTaskBuilder(cc: CommonContext) {
  import cc._

  def apply(tree: Fsm_entityContext): FsmTask = {

    object StatementVisitor extends VScalarVisitor[Stmt] {
      override def visitBlockStmt(ctx: BlockStmtContext) = {
        val stmts = visit(ctx.stmts)
        val ctrlStmts = stmts collect { case s: CtrlStmt => s }
        val combStmts = stmts collect { case s: CombStmt => s }
        val attr = Attr(ctx.loc)

        (ctrlStmts, combStmts) match { // TODO: Not sure this is the best way to write this
          case (Nil, comb) => CombinatorialBlock(attr, comb)
          case (ctrl, comb) => {
            stmts.last match {
              case s: CtrlStmt => ControlBlock(attr, stmts)
              case s: CombStmt => Message.error(ctx, "A control block must end with a control statement"); ErrorStmt(Attr(ctx.loc))
            }
          }
        }
      }

      override def visitDeclStmt(ctx: DeclStmtContext) = {
        val attr = Attr(ctx.loc)
        LookUpDecl(ctx.decl) match {
          case s: DeclVar => DeclarationStmt(attr, s)
          case s: Decl => {
            Message.error(ctx, "Only variable declarations allowed inside functions"); ErrorStmt(attr)
          }
        }
      }

      override def visitIfStmt(ctx: IfStmtContext) = {
        val cond = exprVisitor(ctx.expr())
        val thenStmt = visit(ctx.thenStmt)
        val elseStmt = visit(Option(ctx.elseStmt))
        val attr = Attr(ctx.loc)

        (thenStmt, elseStmt) match {
          case (t: CtrlStmt, None)              => ControlIf(attr, cond, t, None)
          case (t: CtrlStmt, Some(e: CtrlStmt)) => ControlIf(attr, cond, t, Some(e))
          case (t: CombStmt, None)              => CombinatorialIf(attr, cond, t, None)
          case (t: CombStmt, Some(e: CombStmt)) => CombinatorialIf(attr, cond, t, Some(e))
          case _ => {
            Message.error(ctx, "Both branches of an if must be control statements, or both must be combinatorial statements");
            ErrorStmt(attr)
          }
        }
      }

      override def visitCaseStmt(ctx: CaseStmtContext) = {

        object DefaultVisitor extends VScalarVisitor[Option[Stmt]] {
          override val defaultResult = None
          override def visitDefaultCase(ctx: DefaultCaseContext) = Some(StatementVisitor(ctx.statement()))
        }

        object CaseVisitor extends VScalarVisitor[Option[Node]] {
          override val defaultResult = None
          override def visitNormalCase(ctx: NormalCaseContext) = {
            val args = exprVisitor(ctx.commaexpr)
            val attr = Attr(ctx.loc)
            StatementVisitor(ctx.statement()) match {
              case s: CtrlStmt => Some(ControlCaseLabel(attr, args, s))
              case s: CombStmt => Some(CombinatorialCaseLabel(attr, args, s))
            }
          }
        }

        val test = exprVisitor(ctx.expr())

        val defaultCase = DefaultVisitor(ctx.cases).flatten match {
          case Nil      => None
          case d :: Nil => Some(d)
          case _        => Message.error(ctx, "More than one 'default' case item specified"); None
        }

        val cases = CaseVisitor(ctx.cases).flatten
        val ctrlCases = cases collect { case s: ControlCaseLabel => s }
        val combCases = cases collect { case s: CombinatorialCaseLabel => s }
        val attr = Attr(ctx.loc)

        (ctrlCases, combCases, defaultCase) match {
          case (Nil, Nil, None)               => CombinatorialCaseStmt(attr, test, Nil, None)
          case (Nil, Nil, Some(d: CombStmt))  => CombinatorialCaseStmt(attr, test, Nil, Some(d))
          case (Nil, Nil, Some(d: CtrlStmt))  => ControlCaseStmt(attr, test, Nil, Some(d))
          case (Nil, comb, None)              => CombinatorialCaseStmt(attr, test, comb, None)
          case (Nil, comb, Some(d: CombStmt)) => CombinatorialCaseStmt(attr, test, comb, Some(d))
          case (ctrl, Nil, None)              => ControlCaseStmt(attr, test, ctrl, None)
          case (ctrl, Nil, Some(d: CtrlStmt)) => ControlCaseStmt(attr, test, ctrl, Some(d))
          case _ => {
            Message.error(ctx, "Either all or none of the case items must be control statements");
            ErrorStmt(attr)
          }
        }
      }

      override def visitLoopStmt(ctx: LoopStmtContext) = {
        val body = visit(ctx.stmts)
        val attr = Attr(ctx.loc)

        body.last match {
          case _: CombStmt => {
            Message.error(ctx, "The body of a 'loop' must end with a control statement"); ErrorStmt(attr)
          }
          case _ => ControlLoop(attr, ControlBlock(attr, body))
        }
      }

      def loopWarnings(cond: Expr, body: List[Stmt]) = {
        if (cond.isConst) {
          if (cond.eval == 0) {
            Message.warning(cond, "Condition of loop is always false")
          } else {
            Message.warning(cond, "Condition of loop is always true. Use 'loop' instead.")
          }
        }

        body.lastOption foreach {
          _ match {
            case s: FenceStmt => Message.warning(s, "Redundant 'fence' at end of loop body")
            case _            =>
          }
        }
      }

      override def visitWhileStmt(ctx: WhileStmtContext) = {
        val cond = exprVisitor(ctx.expr)
        val body = visit(ctx.stmts)

        loopWarnings(cond, body)

        ControlWhile(Attr(ctx.loc), cond, body)
      }

      override def visitDoStmt(ctx: DoStmtContext) = {
        val cond = exprVisitor(ctx.expr)
        val body = visit(ctx.stmts)

        loopWarnings(cond, body)

        ControlDo(Attr(ctx.loc), cond, body)
      }

      object ForInitVisitor extends VScalarVisitor[(Option[DeclVar], CombStmt)] {
        override def visitForInitNoDecl(ctx: ForInitNoDeclContext) = {
          val stmt = StatementVisitor(ctx.assignment_statement) match {
            case s: CombStmt => s
            case _: CtrlStmt => unreachable
          }
          (None, stmt)
        }
        override def visitDeclVarInit(ctx: DeclVarInitContext) = {
          val varDecl = LookUpDecl(ctx).asInstanceOf[DeclVar]
          val initExpr = Assign(Attr(ctx.loc), LValName(Attr(ctx.IDENTIFIER.loc), ctx.IDENTIFIER :: Nil), exprVisitor(ctx.expr))
          (Some(varDecl), initExpr)
        }
      }

      override def visitForStmt(ctx: ForStmtContext) = {
        val (optDecl, initStmt) = ForInitVisitor(ctx.init)
        val cond = exprVisitor(ctx.cond)
        val stepStmt = visit(ctx.step) match {
          case s: CombStmt => s
          case _: CtrlStmt => unreachable
        }
        val body = visit(ctx.stmts)
        val attr = Attr(ctx.loc)

        loopWarnings(cond, body)

        val forAST = ControlFor(attr, initStmt, cond, stepStmt, body)
        optDecl match {
          case None       => forAST
          case Some(decl) => ControlBlock(attr, DeclarationStmt(attr, decl) :: forAST :: Nil)
        }
      }

      override def visitFenceStmt(ctx: FenceStmtContext) = FenceStmt(Attr(ctx.loc))
      override def visitBreakStmt(ctx: BreakStmtContext) = BreakStmt(Attr(ctx.loc))
      override def visitReturnStmt(ctx: ReturnStmtContext) = ReturnStmt(Attr(ctx.loc))
      override def visitDollarCommentStmt(ctx: DollarCommentStmtContext) = AlogicComment(Attr(ctx.loc), ctx.LITERAL)
      override def visitGotoStmt(ctx: GotoStmtContext) = GotoStmt(Attr(ctx.loc), ctx.IDENTIFIER)

      override def visitAssignmentStmt(ctx: AssignmentStmtContext) = visit(ctx.assignment_statement)

      override def visitAssignInc(ctx: AssignIncContext) = Plusplus(Attr(ctx.loc), lvalVisitor(ctx.lval))
      override def visitAssignDec(ctx: AssignDecContext) = Minusminus(Attr(ctx.loc), lvalVisitor(ctx.lval))
      override def visitAssign(ctx: AssignContext) = Assign(Attr(ctx.loc), lvalVisitor(ctx.lval), exprVisitor(ctx.expr()))
      override def visitAssignUpdate(ctx: AssignUpdateContext) = Update(Attr(ctx.loc), lvalVisitor(ctx.lval), ctx.ASSIGNOP, exprVisitor(ctx.expr()))

      override def visitExprStmt(ctx: ExprStmtContext) = exprVisitor(ctx.expr) match {
        case CallExpr(a, DottedName(_, target :: Nil), Nil) => CallStmt(a, target)
        case CallExpr(_, _, _)                              => unreachable
        case expr => {
          val attr = Attr(ctx.loc)
          if (expr.hasSideEffect) {
            ExprStmt(attr, expr)
          } else {
            Message.error(ctx, "A pure expression in statement position does nothing"); ErrorStmt(attr)
          }
        }
      }
    }

    object FsmTaskVisitor extends VScalarVisitor[FsmTask] {
      object FsmContentVisitor extends VScalarVisitor[Node] {
        override def visitFunction(ctx: FunctionContext) = {
          val name = ctx.IDENTIFIER.text
          val stmts = StatementVisitor(ctx.stmts)
          val attr = Attr(ctx.loc)
          val body = stmts.last match {
            case _: CtrlStmt => ControlBlock(attr, stmts)
            case _: CombStmt => {
              Message.error(ctx, "A function body must end with a control statement"); ErrorStmt(attr)
            }
          }
          Function(attr, name, body)
        }
        override def visitFenceFunction(ctx: FenceFunctionContext) = {
          val attr = Attr(ctx.loc)

          val body = StatementVisitor(ctx.stmts) collect {
            case stmt: CombStmt => stmt
            case stmt: CtrlStmt => Message.error(stmt, "Body of 'fence' function must not contain control statements"); ErrorStmt(attr)
          }
          FenceFunction(attr, CombinatorialBlock(attr, body))
        }
        override def visitVerilogFunction(ctx: VerilogFunctionContext) = VerilogFunctionVisitor(ctx)
      }

      override def visitEntityFSM(ctx: EntityFSMContext) = {
        val name = ctx.IDENTIFIER.text
        val decls = LookUpDecl(ctx.decls)
        val contents = FsmContentVisitor(ctx.contents)
        val fns = contents collect { case x: Function => x }
        val fencefns = contents collect { case x: FenceFunction => x }
        val vfns = contents collect { case x: VerilogFunction => x }
        if (fencefns.length > 1) {
          Message.error(ctx, s"fsm '$name' has more than 1 fence function defined")
        }

        FsmTask(Attr(ctx.loc), name, decls, fns, fencefns.headOption, vfns)
      }
    }

    FsmTaskVisitor(tree)
  }
}

////////////////////////////////////////////////////////////////////////////////
// Builder to handle 'verilog' task definitions
////////////////////////////////////////////////////////////////////////////////
class VerilogTaskBuilder(cc: CommonContext) {
  import cc._

  def apply(tree: EntityVerilogContext): VerilogTask = {

    object VerilogTaskVisitor extends VScalarVisitor[VerilogTask] {
      override def visitEntityVerilog(ctx: EntityVerilogContext) = {
        val vfns = ctx.contents.toList collect {
          case c: VerilogFunctionContext => VerilogFunctionVisitor(c)
        }
        VerilogTask(Attr(ctx.loc), ctx.IDENTIFIER.text, LookUpDecl(ctx.decls), vfns)
      }
    }

    VerilogTaskVisitor(tree)
  }
}

////////////////////////////////////////////////////////////////////////////////
// Builder to handle 'network' definitions
////////////////////////////////////////////////////////////////////////////////
class NetworkTaskBuilder(cc: CommonContext) {
  import cc._

  lazy val fsmTaskBuilder = new FsmTaskBuilder(cc)

  def apply(tree: Network_entityContext): NetworkTask = {

    object DottedNameVisitor extends VScalarVisitor[DottedName] {
      override def visitDotted_name(ctx: Dotted_nameContext) = DottedName(Attr(ctx.loc), ctx.es.toList map (_.text))
    }

    object NetworkVisitor extends VScalarVisitor[NetworkTask] {
      object NetworkContentVisitor extends VScalarVisitor[List[Node]] {
        override def visitNetworkContentFSM(ctx: NetworkContentFSMContext) = {
          val fsm = fsmTaskBuilder(ctx.fsm_entity)

          if (Option(ctx.autoinst).isDefined) {
            fsm :: Instantiate(Attr(ctx.loc), fsm.name, fsm.name, ListMap.empty) :: Nil
          } else {
            fsm :: Nil
          }
        }
        override def visitConnect(ctx: ConnectContext) = {
          val lhs = DottedNameVisitor(ctx.lhs)
          val rhs = DottedNameVisitor(ctx.rhs)
          Connect(Attr(ctx.loc), lhs, rhs) :: Nil
        }
        override def visitInstantiate(ctx: InstantiateContext) = {
          val id = ctx.IDENTIFIER(0).text
          val module = ctx.IDENTIFIER(1).text
          val pas = ctx.param_args.param_assign.toList map { pa =>
            pa.IDENTIFIER.text -> exprVisitor(pa.expr)
          }
          Instantiate(Attr(ctx.loc), id, module, ListMap(pas: _*)) :: Nil
        }
        override def visitVerilogFunction(ctx: VerilogFunctionContext) = VerilogFunctionVisitor(ctx) :: Nil
      }

      override def visitEntityNetwork(ctx: EntityNetworkContext) = {
        val name = ctx.IDENTIFIER.text
        val decls = LookUpDecl(ctx.decls)
        val contents = NetworkContentVisitor(ctx.contents).flatten
        val inst = contents collect { case x: Instantiate => x }
        val conn = contents collect { case x: Connect => x }
        val vfns = contents collect { case x: VerilogFunction => x }
        val fsms = contents collect { case x: FsmTask => x }

        NetworkTask(Attr(ctx.loc), name, decls, inst, conn, vfns, fsms)
      }
    }
    NetworkVisitor(tree)
  }
}

object AstBuilder {
  def apply(root: ParserRuleContext, initialTypedefs: Map[String, Type] = Map[String, Type]()): Task = {

    val cc = new CommonContext(root, initialTypedefs)

    lazy val fsmTaskBuilder = new FsmTaskBuilder(cc)
    lazy val verilogTaskBuilder = new VerilogTaskBuilder(cc)
    lazy val networkTaskBuilder = new NetworkTaskBuilder(cc)

    object RootVisitor extends VScalarVisitor[Task] {
      override def visitEntityFSM(ctx: EntityFSMContext) = fsmTaskBuilder(ctx)
      override def visitEntityVerilog(ctx: EntityVerilogContext) = verilogTaskBuilder(ctx)
      override def visitEntityNetwork(ctx: EntityNetworkContext) = networkTaskBuilder(ctx)
    }

    RootVisitor(cc.entityCtx)
  }
}
