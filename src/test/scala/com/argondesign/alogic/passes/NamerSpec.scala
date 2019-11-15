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
// Namer tests
////////////////////////////////////////////////////////////////////////////////

package com.argondesign.alogic.passes

import com.argondesign.alogic.AlogicTest
import com.argondesign.alogic.SourceTextConverters._
import com.argondesign.alogic.ast.Trees._
import com.argondesign.alogic.core.CompilerContext
import com.argondesign.alogic.core.Error
import com.argondesign.alogic.core.Symbols.Symbol
import com.argondesign.alogic.core.Types.TypeNum
import com.argondesign.alogic.core.Types.TypeUInt
import com.argondesign.alogic.core.Warning
import com.argondesign.alogic.core.enums.EntityVariant
import org.scalatest.FreeSpec

final class NamerSpec extends FreeSpec with AlogicTest {

  implicit val cc: CompilerContext = new CompilerContext
  lazy val atBits = ExprSym(cc.lookupGlobalTerm("@bits"))
  val namer = new Namer

  def xform(tree: Tree): Tree = {
    tree match {
      case Root(decls) => cc.addGlobalDecls(decls.collect { case decl: Decl => decl })
      case decl: Decl => cc.addGlobalDecl(decl)
      case _ =>
    }
    tree rewrite namer
  }

  "The Namer should " - {
    "issue error for redefinition of variable" in {
      """|{
         |  u1 foo;
         |  u2 foo;
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages should have length 1
      cc.messages(0) should beThe[Error](
        "Redefinition of 'foo' with previous definition at",
        ".*:2"
      )
      cc.messages(0).loc.line shouldBe 3
    }

    "issue error for redefinition of type" in {
      xform {
        """|fsm a {
           |  typedef u1 foo;
           |  typedef u2 foo;
           |}""".stripMargin.asTree[Decl]
      }

      cc.messages.loneElement should beThe[Error](
        "Redefinition of 'foo' with previous definition at",
        ".*:2"
      )
      cc.messages(0).loc.line shouldBe 3
    }

    "issue warning for variable hiding" in {
      """|{
         |  u1 foo;
         |  { u2 foo; }
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages should have length 1
      cc.messages(0) should beThe[Warning](
        "Definition of 'foo' hides previous definition at",
        ".*:2"
      )
      cc.messages(0).loc.line shouldBe 3
    }

    "not issue warning for variable hiding for later symbol" in {
      """|{
         |  { u2 foo; }
         |  u1 foo;
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages shouldBe empty
    }

    "cope with using the same name in non-intersecting scopes" in {
      """|{
         |  { u1 foo; }
         |  { u2 foo; }
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages shouldBe empty
    }

    "cope with multi level typedefs" in {
      val root = """|typedef bool a;
                    |typedef a b;
                    |fsm c {}""".stripMargin.asTree[Root]
      xform(root)

      cc.messages shouldBe empty
    }

    "issue error for use before definition for symbols defined in statements" in {
      """|{
         |  u1 foo = bar;
         |  u1 bar;
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages.loneElement should beThe[Error]("'bar' used before it is defined")
      cc.messages.loneElement.loc.line shouldBe 2
    }

    "not issue error for use before definition for symbols not defined in statements" in {
      val tree = """|fsm a {
                    |  void main() {
                    |    foo();
                    |  }
                    |  void foo() {}
                    |}""".stripMargin.asTree[Decl]

      xform(tree)

      cc.messages shouldBe empty
    }

    "issue error for undefined term names" in {
      """|{
         |  u1 foo = bar;
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages should have length 1
      cc.messages(0) should beThe[Error]("'bar' is not defined")
      cc.messages(0).loc.line shouldBe 2
    }

    "issue error for undefined type names" in {
      """|{
         |  foo_t foo;
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages should have length 1
      cc.messages(0) should beThe[Error]("'foo_t' is not defined")
      cc.messages(0).loc.line shouldBe 2
    }

    "insert names from 'for ()' loop initializers into the loop scope" in {
      """|for (bool b=true;;) {
         | i2 b;
         |}""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages should have length 1
      cc.messages(0) should beThe[Warning](
        "Definition of 'b' hides previous definition at",
        ".*:1"
      )
      cc.messages(0).loc.line shouldBe 2
    }

    "insert names from 'let ()' initializers into the following loop scope" in {
      """|let (bool a=true) do {
         | i2 a;
         |} while (1);""".stripMargin.asTree[Stmt] rewrite namer

      cc.messages should have length 1
      cc.messages(0) should beThe[Warning](
        "Definition of 'a' hides previous definition at",
        ".*:1"
      )
      cc.messages(0).loc.line shouldBe 2
    }

    "resolve term names to their correct definitions" in {
      val tree = """|{
                    |  bool a;
                    |  {
                    |    bool a;
                    |    a = false;
                    |  }
                    |  a = true;
                    |}""".stripMargin.asTree[Stmt] rewrite namer

      inside(tree) {
        case StmtBlock(
            List(StmtDecl(Decl(Sym(outer1, _), _)), block, StmtAssign(ExprSym(outer2), _))) =>
          outer1.loc.line shouldBe 2
          outer1 should be theSameInstanceAs outer2
          inside(block) {
            case StmtBlock(
                List(StmtDecl(Decl(Sym(inner1, _), _)), StmtAssign(ExprSym(inner2), _))) =>
              inner1.loc.line shouldBe 4
              inner1 should be theSameInstanceAs inner2
              inner1 shouldNot be theSameInstanceAs outer1
          }
      }

      cc.messages.loneElement should beThe[Warning](
        "Definition of 'a' hides previous definition at",
        ".*:2"
      )
    }

    "resolve term names to their correct definitions - builtin" in {
      val tree = "@bits".asTree[Expr] rewrite namer

      tree shouldBe atBits
      cc.messages shouldBe empty
    }

    "resolve term names to their correct definitions - dict a" in {
      val root = """|network a {
                    |  gen for (uint N < 10) {
                    |    in bool i#[N];
                    |    out bool o#[N];
                    |    i#[N] -> o#[N];
                    |  }
                    |}""".stripMargin.asTree[Root]

      inside(xform(root)) {
        case Root(List(RizDecl(Decl(_, DescEntity(EntityVariant.Net, ents))))) =>
          inside(ents) {
            case List(EntGen(GenRange(Decl(Sym(nSym, _), _), _, _, body)), _, _) =>
              inside(body) {
                case Decl(Sym(dISym, ExprSym(nASym) :: Nil), _) ::
                      Decl(Sym(dOSym, ExprSym(nBSym) :: Nil), _) ::
                      EntConnect(
                      ExprRef(Sym(cISym, ExprSym(nCSym) :: Nil)),
                      ExprRef(Sym(cOSym, ExprSym(nDSym) :: Nil)) :: Nil
                    ) :: Nil =>
                  dISym should be theSameInstanceAs cISym
                  dOSym should be theSameInstanceAs cOSym
                  nSym should be theSameInstanceAs nASym
                  nSym should be theSameInstanceAs nBSym
                  nSym should be theSameInstanceAs nCSym
                  nSym should be theSameInstanceAs nDSym
              }
          }
      }

      cc.emitMessages()
      cc.messages shouldBe empty
    }

    "resolve term names to their correct definitions - dict b" in {
      val root = """|network a {
                    |  gen for (uint N < 2) {
                    |    in bool i#[N];
                    |    out bool o#[N];
                    |  }
                    |  i#[0] -> o#[0];
                    |  i#[1] -> o#[1];
                    |}""".stripMargin.asTree[Root]

      inside(xform(root)) {
        case Root(List(RizDecl(Decl(_, DescEntity(EntityVariant.Net, ents))))) =>
          inside(ents) {
            case List(EntGen(GenRange(_, _, _, body)), conn0, conn1, _, _) =>
              inside(body) {
                case Decl(Sym(iSym, _), _) ::
                      Decl(Sym(oSym, _), _) :: Nil =>
                  inside(conn0) {
                    case EntConnect(
                        ExprRef(Sym(lSym, Expr(0) :: Nil)),
                        ExprRef(Sym(rSym, Expr(0) :: Nil)) :: Nil
                        ) =>
                      iSym shouldBe theSameInstanceAs(lSym.kind.asChoice.symbols.head)
                      oSym shouldBe theSameInstanceAs(rSym.kind.asChoice.symbols.head)
                  }
                  inside(conn1) {
                    case EntConnect(
                        ExprRef(Sym(lSym, Expr(1) :: Nil)),
                        ExprRef(Sym(rSym, Expr(1) :: Nil)) :: Nil
                        ) =>
                      iSym shouldBe theSameInstanceAs(lSym.kind.asChoice.symbols.head)
                      oSym shouldBe theSameInstanceAs(rSym.kind.asChoice.symbols.head)
                  }
              }
          }
      }

      cc.messages shouldBe empty
    }

    "resolve type names to their correct definitions - typedef" in {
      val root = """|typedef bool foo_t;
                    |
                    |fsm a {
                    |  fence {
                    |    { bool foo_t = 0; }
                    |    foo_t b;
                    |  }
                    |}""".stripMargin.asTree[Root]

      inside(xform(root)) {
        case Root(List(RizDecl(defn), RizDecl(entity))) =>
          inside(defn) {
            case Decl(Sym(defSym, _), _: DescType) =>
              defSym.loc.line shouldBe 1
              inside(entity) {
                case Decl(_, DescEntity(EntityVariant.Fsm, List(EntCombProcess(List(_, stmt))))) =>
                  inside(stmt) {
                    case StmtDecl(Decl(Sym(symbol, _), DescVar(ExprSym(`defSym`), _))) =>
                      symbol.loc.line shouldBe 6
                  }
              }
          }
      }

      cc.messages.loneElement should beThe[Warning](
        "Definition of 'foo_t' hides previous definition at",
        ".*:1"
      )
      cc.messages.loneElement.loc.line shouldBe 5
    }

    "resolve type names to their correct definitions - struct" in {
      val root = """|struct bar_t {
                    |  bool a;
                    |}
                    |
                    |fsm a {
                    |  fence {
                    |    { bool bar_t; }
                    |    bar_t b;
                    |  }
                    |}""".stripMargin.asTree[Root]

      inside(xform(root)) {
        case Root(List(RizDecl(record), RizDecl(entity))) =>
          inside(record) {
            case Decl(Sym(cSymbol, Nil), _: DescRecord) =>
              cSymbol.loc.line shouldBe 1
              inside(entity) {
                case Decl(_, DescEntity(EntityVariant.Fsm, List(EntCombProcess(List(_, stmt))))) =>
                  inside(stmt) {
                    case StmtDecl(Decl(Sym(symbol, _), DescVar(ExprSym(`cSymbol`), _))) =>
                      symbol.loc.line shouldBe 8
                  }
              }
          }
      }

      cc.messages.loneElement should beThe[Warning](
        "Definition of 'bar_t' hides previous definition at",
        ".*:1"
      )
      cc.messages.loneElement.loc.line shouldBe 7
    }

    "resolve function references to later definitions" in {
      val entity = """|fsm a {
                      |  void main () { foo(); }
                      |  void foo () {}
                      |}""".stripMargin.asTree[Decl]

      inside(xform(entity)) {
        case Decl(_, DescEntity(EntityVariant.Fsm, List(main, foo))) =>
          inside(main) {
            case EntDecl(
                Decl(_, DescFunc(_, _, _, List(StmtExpr(ExprCall(ExprSym(fooInMain), _)))))) =>
              inside(foo) {
                case EntDecl(Decl(Sym(fooInDef, Nil), _)) =>
                  fooInMain should be theSameInstanceAs fooInDef
              }
          }
      }

      cc.messages shouldBe empty
    }

    "resolve entity symbols in instantiations" in {
      val entityA = """fsm a {}""".stripMargin.asTree[Decl]
      val entityB = """|network b {
                       |  i = new a();
                       |}""".stripMargin.asTree[Decl]

      cc.addGlobalDecls(List(entityA, entityB))

      val treeA = entityA rewrite namer
      val treeB = entityB rewrite new Namer

      val aSym = treeA match {
        case Decl(Sym(symbol, Nil), _) => symbol
        case _                         => fail
      }

      inside(treeB) {
        case Decl(_, DescEntity(_, List(instance))) =>
          inside(instance) {
            case EntDecl(Decl(_, DescInstance(ExprCall(ExprSym(sym), Nil)))) =>
              sym should be theSameInstanceAs aSym
          }
      }
    }

    "resolve goto targets" in {
      val entity = """|fsm a {
                      |  void main() { goto foo; }
                      |  void foo() {}
                      |}""".stripMargin.asTree[Decl]

      inside(xform(entity)) {
        case Decl(_, DescEntity(EntityVariant.Fsm, List(main, foo))) =>
          inside(main) {
            case EntDecl(Decl(Sym(_, Nil), DescFunc(_, _, _, List(StmtGoto(ExprSym(sym)))))) =>
              inside(foo) {
                case EntDecl(Decl(Sym(fooSym, Nil), _)) =>
                  sym should be theSameInstanceAs fooSym
              }
          }
      }

      cc.messages shouldBe empty
    }

    "resolve names inside type arguments" in {
      val block = """|{
                     |  i8 a;
                     |  i8 b;
                     |  int(b)[a] c;
                     |}""".stripMargin.asTree[Stmt]

      val tree = block rewrite namer

      inside(tree) {
        case StmtBlock(List(StmtDecl(declA: Decl), StmtDecl(declB: Decl), StmtDecl(declC: Decl))) =>
          val symA = declA.symbol
          val symB = declB.symbol
          inside(declC) {
            case Decl(_, DescVar(ExprIndex(et, sz), _)) =>
              inside(sz) {
                case ExprSym(sym) =>
                  sym should be theSameInstanceAs symA
              }
              inside(et) {
                case ExprCall(ExprType(TypeNum(true)), List(ArgP(ExprSym(sym)))) =>
                  sym should be theSameInstanceAs symB
              }
          }
      }

      cc.messages shouldBe empty
    }

    "resolve names inside array dimension" in {
      val block = """|{
                     |  i8 a;
                     |  bool b[a];
                     |}""".stripMargin.asTree[Stmt]

      val tree = block rewrite namer

      inside(tree) {
        case StmtBlock(List(StmtDecl(declA: Decl), StmtDecl(declB: Decl))) =>
          val symA = declA.symbol
          inside(declB) {
            case Decl(_, DescArray(ExprType(TypeUInt(w)), sz)) if w == 1 =>
              inside(sz) {
                case ExprSym(sym) =>
                  sym should be theSameInstanceAs symA
              }
          }
      }

      cc.messages shouldBe empty
    }

    "resolve names inside type expressions" in {
      val block = "uint($clog2(1368))".asTree[Expr]

      val tree = block rewrite namer

      tree should matchPattern {
        case ExprCall(ExprType(TypeNum(false)), List(ArgP(ExprCall(ExprSym(_), List(ArgP(_)))))) =>
      }
      cc.messages shouldBe empty
    }

    "use unique symbols in definitions" in {
      val block = """|fsm a {
                     |  i8 a;
                     |}""".stripMargin.asTree[Root]

      val tree = block rewrite namer

      cc.messages shouldBe empty

      inside(tree) {
        case Root(List(RizDecl(Decl(Sym(outerA, _), DescEntity(_, List(decl)))))) =>
          inside(decl) {
            case EntDecl(Decl(Sym(innerA, _), _)) =>
              outerA shouldNot be theSameInstanceAs innerA
          }
      }
    }

    "attach source attributes to symbols - function" in {
      val entity = "fsm foo { (* reclimit = 1 *) void a() {} }".asTree[Decl]
      val tree = xform(entity)

      val symA = tree getFirst {
        case Sym(symbol, Nil) if symbol.name == "a" => symbol
      }
      symA.attr.recLimit.get.value shouldBe Expr(1)
    }

    "attach source attributes to symbols - entity" in {
      val entity = "(* stacklimit = 2 *) fsm foo { }".asTree[Decl]
      val tree = xform(entity)

      val symA = tree getFirst { case Decl(Sym(symbol, Nil), _) if symbol.name == "foo" => symbol }
      symA.attr.stackLimit.get.value shouldBe Expr(2)
    }

    "attach source attributes to symbols - nested entity" in {
      val entity = "network foo { (* stacklimit = 3 *) fsm bar {} }".asTree[Decl]
      val tree = xform(entity)

      val symA = tree getFirst { case Decl(Sym(symbol, Nil), _) if symbol.name == "bar" => symbol }
      symA.attr.stackLimit.get.value shouldBe Expr(3)
    }

    "attach source attributes to symbols - declaration" in {
      val entity = "fsm foo { (* unused *) i8 a; }".asTree[Decl]
      val tree = xform(entity)

      val symA = tree getFirst { case Decl(Sym(symbol, Nil), _: DescVar) => symbol }
      symA.attr.unused.get.value shouldBe true
    }

    "check dictionary identifier declarations only appear inside 'gen' loops" - {
      "entity" - {
        for {
          (variant, text) <- List(
            ("network", "bool a#[0];"),
            ("network", "typedef bool a#[0];"),
            ("network", "fsm a#[0] {}"),
            ("network", "a#[0] = new e();"),
            ("fsm ", "void a#[0]() {}")
          )
        } {
          val error =
            "Definition with dictionary identifier must appear directly in 'gen' loop scope."
          text - {
            "entity" in {
              xform(s"$variant e {$text}".asTree[Root])
              cc.messages.loneElement should beThe[Error](error)
            }

            "gen if" in {
              xform(s"$variant e { gen if (true) {$text} }".asTree[Root])
              cc.messages.loneElement should beThe[Error](error)
            }

            "gen else" in {
              xform(s"$variant e { gen if (false) {} else {$text} }".asTree[Root])
              cc.messages.loneElement should beThe[Error](error)
            }

            "gen for" in {
              xform(s"$variant e { gen for (uint N = 0; N < 0 ; N++) {$text} }".asTree[Root])
              cc.messages shouldBe empty
            }

            "gen range" in {
              xform(s"$variant e { gen for (uint N < 0) {$text} }".asTree[Root])
              cc.messages shouldBe empty
            }
          }
        }
      }

      "stmt" - {
        val text = "bool a#[0];"
        val error =
          "Definition with dictionary identifier must appear directly in 'gen' loop scope."

        "gen if" in {
          s"{gen if (true) {$text}}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "gen else" in {
          s"{gen if (true) {} else {$text}}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "gen for" in {
          s"{gen for (uint N = 0; N < 0 ; N++) {$text}}".asTree[Stmt] rewrite namer
          cc.messages shouldBe empty
        }

        "gen range" in {
          s"{gen for (uint N < 0) {$text}}".asTree[Stmt] rewrite namer
          cc.messages shouldBe empty
        }

        "block gen if" in {
          s"{gen if (true) {{$text}}}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "block gen else" in {
          s"{gen if (true) {} else {{$text}}}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "block in gen for" in {
          s"{gen for (uint N = 0; N < 0 ; N++) {{$text}}}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "block in gen range" in {
          s"{gen for (uint N < 0) {{$text}}}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "block" in {
          s"{$text}".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "if" in {
          s"if (true) $text".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "else" in {
          s"if (true) {} else $text".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "case clause - regular" in {
          s"case (1) { 0: $text }".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }

        "case clause - default" in {
          s"case (1) { default: $text }".asTree[Stmt] rewrite namer
          cc.messages.loneElement should beThe[Error](error)
        }
      }
    }

    "add choice symbol definitions" - {
      @scala.annotation.tailrec
      def checkUnique(symbol: Symbol*): Unit = symbol match {
        case s +: ss =>
          ss foreach {
            s shouldNot be theSameInstanceAs _
          }
          checkUnique(ss: _*)
        case _ =>
      }

      "correctness" - {

        "if then" in {
          val tree = xform {
            """|{
               |  gen if (1) {
               |    bool a;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen), StmtDecl(decl))) =>
              inside(gen) {
                case GenIf(_, List(Decl(Sym(a0, _), _: DescVar)), Nil) =>
                  inside(decl) {
                    case Decl(Sym(c, _), DescChoice(List(ExprSym(`a0`)))) =>
                      checkUnique(c, a0)
                  }
              }
          }
        }

        "if else" in {
          val tree = xform {
            """|{
               |  gen if (1) {} else {
               |    bool a;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen), StmtDecl(decl))) =>
              inside(gen) {
                case GenIf(_, Nil, List(Decl(Sym(a0, _), _: DescVar))) =>
                  inside(decl) {
                    case Decl(Sym(c, _), DescChoice(List(ExprSym(`a0`)))) =>
                      checkUnique(c, a0)
                  }
              }
          }
        }


        "if then else" in {
          val tree = xform {
            """|{
               |  gen if (1) {
               |    bool a;
               |  } else {
               |    bool a;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen), StmtDecl(decl))) =>
              inside(gen) {
                case GenIf(_,
                List(Decl(Sym(a0, _), _: DescVar)),
                List(Decl(Sym(a1, _), _: DescVar))) =>
                  inside(decl) {
                    case Decl(Sym(c, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                      checkUnique(c, a0, a1)
                  }
              }
          }
        }

        "multiple if then " in {
          val tree = xform {
            """|{
               |  gen if (1) {
               |    bool a;
               |  }
               |  gen if (1) {
               |    bool a;
               |  }
               |  gen if (1) {
               |    bool a;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen0), StmtGen(gen1), StmtGen(gen2), StmtDecl(decl))) =>
              inside(gen0) {
                case GenIf(_, List(Decl(Sym(a0, _), _: DescVar)), Nil) =>
                  inside(gen1) {
                    case GenIf(_, List(Decl(Sym(a1, _), _: DescVar)), Nil) =>
                      inside(gen2) {
                        case GenIf(_, List(Decl(Sym(a2, _), _: DescVar)), Nil) =>
                          inside(decl) {
                            case Decl(Sym(c, _),
                            DescChoice(
                            List(ExprSym(`a2`), ExprSym(`a1`), ExprSym(`a0`)))) =>
                              checkUnique(c, a0, a1, a2)
                          }
                      }
                  }
              }
          }
        }

        "multiple if then else" in {
          val tree = xform {
            """|{
               |  gen if (1) {
               |    bool a;
               |  } else {
               |    bool a;
               |  }
               |  gen if (1) {
               |    bool a;
               |  } else {
               |    bool a;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen0), StmtGen(gen1), StmtDecl(decl))) =>
              inside(gen0) {
                case GenIf(_,
                List(Decl(Sym(a0, _), _: DescVar)),
                List(Decl(Sym(a1, _), _: DescVar))) =>
                  inside(gen1) {
                    case GenIf(_,
                    List(Decl(Sym(a2, _), _: DescVar)),
                    List(Decl(Sym(a3, _), _: DescVar))) =>
                      inside(decl) {
                        case Decl(
                        Sym(c, _),
                        DescChoice(
                        List(ExprSym(`a3`), ExprSym(`a2`), ExprSym(`a1`), ExprSym(`a0`)))) =>
                          checkUnique(c, a0, a1, a2, a3)
                      }
                  }
              }
          }
        }

        "nested if then" in {
          val tree = xform {
            """|{
               |  gen if (1) {
               |    gen if (1) {
               |      bool a;
               |    }
               |  } else {
               |    gen if (1) {
               |      bool a;
               |    }
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen), StmtDecl(decl))) =>
              inside(gen) {
                case GenIf(_,
                List(GenIf(_, List(Decl(Sym(a0, _), _: DescVar)), Nil), d0),
                List(GenIf(_, List(Decl(Sym(a1, _), _: DescVar)), Nil), d1)) =>
                  inside(d0) {
                    case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a0`)))) =>
                      inside(d1) {
                        case Decl(Sym(c1, _), DescChoice(List(ExprSym(`a1`)))) =>
                          inside(decl) {
                            case Decl(Sym(c, _), DescChoice(List(ExprSym(`c1`), ExprSym(`c0`)))) =>
                              checkUnique(c, c0, c1, a0, a1)
                          }
                      }
                  }
              }
          }
        }

        "nested if then else" in {
          val tree = xform {
            """|{
               |  gen if (1) {
               |    gen if (1) {
               |      bool a;
               |    } else {
               |      bool a;
               |    }
               |  } else {
               |    gen if (1) {
               |      bool a;
               |    } else {
               |      bool a;
               |    }
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen), StmtDecl(decl))) =>
              inside(gen) {
                case GenIf(_,
                List(GenIf(_,
                List(Decl(Sym(a0, _), _: DescVar)),
                List(Decl(Sym(a1, _), _: DescVar))),
                d0),
                List(GenIf(_,
                List(Decl(Sym(a2, _), _: DescVar)),
                List(Decl(Sym(a3, _), _: DescVar))),
                d1)) =>
                  inside(d0) {
                    case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                      inside(d1) {
                        case Decl(Sym(c1, _), DescChoice(List(ExprSym(`a3`), ExprSym(`a2`)))) =>
                          inside(decl) {
                            case Decl(Sym(c, _), DescChoice(List(ExprSym(`c1`), ExprSym(`c0`)))) =>
                              checkUnique(c, c0, c1, a0, a1, a2, a3)
                          }
                      }
                  }
              }
          }
        }

        "for" in {
          val tree = xform {
            """|{
               |  gen for(uint N = 0 ; N < 1 ; N++) {
               |    bool a#[N];
               |    bool b;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen), StmtDecl(decl))) =>
              inside(gen) {
                case GenFor(_, _, _, List(Decl(Sym(a0, _), _: DescVar), _: Decl)) =>
                  inside(decl) {
                    case Decl(Sym(c, _), DescChoice(List(ExprSym(`a0`)))) =>
                      checkUnique(c, a0)
                      c.name shouldBe "a"
                  }
              }
          }
        }

        "multiple for" in {
          val tree = xform {
            """|{
               |  gen for(uint N = 0 ; N < 1 ; N++) {
               |    bool a#[N];
               |    bool b;
               |  }
               |  gen for(uint N = 0 ; N < 1 ; N++) {
               |    bool a#[N];
               |    bool b;
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(gen0), StmtGen(gen1), StmtDecl(decl))) =>
              inside(gen0) {
                case GenFor(_, _, _, List(Decl(Sym(a0, _), _: DescVar), _: Decl)) =>
                  inside(gen1) {
                    case GenFor(_, _, _, List(Decl(Sym(a1, _), _: DescVar), _: Decl)) =>
                      inside(decl) {
                        case Decl(Sym(c, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                          checkUnique(c, a0, a1)
                          c.name shouldBe "a"
                      }
                  }
              }
          }
        }

        "for if " in {
          val tree = xform {
            """|{
               |  gen for (uint N = 0 ; N < 1 ; N++) {
               |    gen if (1) {
               |      bool a#[N];
               |      bool b;
               |    }
               |  }
               |}""".stripMargin.asTree[Stmt]
          }

          inside(tree) {
            case StmtBlock(List(StmtGen(genFor), StmtDecl(decl))) =>
              inside(genFor) {
                case GenFor(_, _, _, List(genIf, d0, d1)) =>
                  inside(genIf) {
                    case GenIf(_, List(Decl(Sym(a0, _), _: DescVar), Decl(Sym(b0, _), _: DescVar)), Nil) =>
                      inside(d0) {
                        case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a0`)))) =>
                          inside(d1) {
                            case Decl(Sym(c1, _), DescChoice(List(ExprSym(`b0`)))) =>
                              inside(decl) {
                                case Decl(Sym(c, _), DescChoice(List(ExprSym(`c0`)))) =>
                                  checkUnique(c, c0, a0, b0)
                              }
                          }
                      }
                  }
              }
          }
        }

      }

      "position" - {

        "decl" - {
          "entity" in {
            val tree = xform {
              """|fsm foo {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Decl]
            }

            inside(tree) {
              case Decl(_, DescEntity(_, List(EntGen(gen), EntDecl(decl)))) =>
                inside(gen) {
                  case GenIf(_,
                             List(Decl(Sym(a0, _), _: DescVar)),
                             List(Decl(Sym(a1, _), _: DescVar))) =>
                    inside(decl) {
                      case Decl(Sym(c, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                        checkUnique(c, a0, a1)
                    }
                }
            }
          }

          // Record..

          "singleton" in {
            val tree = xform {
              """|new fsm foo {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Decl]
            }

            inside(tree) {
              case Decl(_, DescSingleton(_, List(EntGen(gen), EntDecl(decl)))) =>
                inside(gen) {
                  case GenIf(_,
                             List(Decl(Sym(a0, _), _: DescVar)),
                             List(Decl(Sym(a1, _), _: DescVar))) =>
                    inside(decl) {
                      case Decl(Sym(c, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                        checkUnique(c, a0, a1)
                    }
                }
            }
          }

          "func" in {
            val tree = xform {
              """|void foo() {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Decl]
            }

            inside(tree) {
              case Decl(_, DescFunc(_, _, _, List(StmtGen(gen), StmtDecl(decl)))) =>
                inside(gen) {
                  case GenIf(_,
                             List(Decl(Sym(a0, _), _: DescVar)),
                             List(Decl(Sym(a1, _), _: DescVar))) =>
                    inside(decl) {
                      case Decl(Sym(c, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                        checkUnique(c, a0, a1)
                    }
                }
            }
          }

        }

        "gen" - {

          "if then" in {
            val tree = xform {
              """|gen if (1) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Gen]
            }

            inside(tree) {
              case GenIf(_,
                         List(GenIf(_,
                                    List(Decl(Sym(a0, _), _: DescVar)),
                                    List(Decl(Sym(a1, _), _: DescVar))),
                              d0),
                         Nil) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "if else" in {
            val tree = xform {
              """|gen if (1) {} else {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Gen]
            }

            inside(tree) {
              case GenIf(_,
                         Nil,
                         List(GenIf(_,
                                    List(Decl(Sym(a0, _), _: DescVar)),
                                    List(Decl(Sym(a1, _), _: DescVar))),
                              d0)) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "if then else" in {
            val tree = xform {
              """|gen if (1) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |} else {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Gen]
            }

            inside(tree) {
              case GenIf(_,
                         List(GenIf(_,
                                    List(Decl(Sym(a0, _), _: DescVar)),
                                    List(Decl(Sym(a1, _), _: DescVar))),
                              d0),
                         List(GenIf(_,
                                    List(Decl(Sym(a2, _), _: DescVar)),
                                    List(Decl(Sym(a3, _), _: DescVar))),
                              d1)) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    inside(d1) {
                      case Decl(Sym(c1, _), DescChoice(List(ExprSym(`a3`), ExprSym(`a2`)))) =>
                        checkUnique(c0, c1, a0, a1, a2, a3)
                    }
                }
            }
          }

          "for" in {
            val tree = xform {
              """|gen for (u8 a = 0 ; a < 10 ; a++) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Gen]
            }

            inside(tree) {
              case GenFor(_,
                          _,
                          _,
                          List(GenIf(_,
                                     List(Decl(Sym(a0, _), _: DescVar)),
                                     List(Decl(Sym(a1, _), _: DescVar))),
                               d0)) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "range" in {
            val tree = xform {
              """|gen for (u8 a < 10) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Gen]
            }

            inside(tree) {
              case GenRange(_,
                            _,
                            _,
                            List(GenIf(_,
                                       List(Decl(Sym(a0, _), _: DescVar)),
                                       List(Decl(Sym(a1, _), _: DescVar))),
                                 d0)) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

        }

        "ent" - {
          "comb process" in {
            val tree = xform {
              """|fence {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Ent]
            }

            inside(tree) {
              case EntCombProcess(List(StmtGen(gen), StmtDecl(decl))) =>
                inside(gen) {
                  case GenIf(_,
                             List(Decl(Sym(a0, _), _: DescVar)),
                             List(Decl(Sym(a1, _), _: DescVar))) =>
                    inside(decl) {
                      case Decl(Sym(c, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                        checkUnique(c, a0, a1)
                    }
                }
            }
          }
        }

        "stmt" - {
          "block" in {
            val tree = xform {
              """|{
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtBlock(
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0))) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "if then" in {
            val tree = xform {
              """|if (1) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtIf(_,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              Nil) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "if else" in {
            val tree = xform {
              """|if (1) {} else {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtIf(_,
              Nil,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0))) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "if then else" in {
            val tree = xform {
              """|if (1) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |} else {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtIf(_,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a2, _), _: DescVar)),
              List(Decl(Sym(a3, _), _: DescVar)))),
              StmtDecl(d1))) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    inside(d1) {
                      case Decl(Sym(c1, _), DescChoice(List(ExprSym(`a3`), ExprSym(`a2`)))) =>
                        checkUnique(c0, c1, a0, a1, a2, a3)
                    }
                }
            }
          }

          "case regular" in {
            val tree = xform {
              """|case (1) {
                 |  1: gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtCase(_,
              List(CaseRegular(_, List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0))))) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "case default" in {
            val tree = xform {
              """|case (1) {
                 |  default: gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtCase(_,
              List(CaseDefault(List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0))))) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "loop" in {
            val tree = xform {
              """|loop {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtLoop(
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              ) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "do" in {
            val tree = xform {
              """|do {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |} while (1);""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtDo(_,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              ) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "while" in {
            val tree = xform {
              """|while (1) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtWhile(_,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              ) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "for" in {
            val tree = xform {
              """|for (u8 a = 0 ; a < 10 ; a++) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }

            inside(tree) {
              case StmtFor(_,
              _,
              _,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              ) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }

          "let" in {
            val tree = xform {
              """|let (u8 a = 0) {
                 |  gen if (1) {
                 |    bool a;
                 |  } else {
                 |    bool a;
                 |  }
                 |}""".stripMargin.asTree[Stmt]
            }


            inside(tree) {
              case StmtLet(_,
              List(StmtGen(
              GenIf(_,
              List(Decl(Sym(a0, _), _: DescVar)),
              List(Decl(Sym(a1, _), _: DescVar)))),
              StmtDecl(d0)),
              ) =>
                inside(d0) {
                  case Decl(Sym(c0, _), DescChoice(List(ExprSym(`a1`), ExprSym(`a0`)))) =>
                    checkUnique(c0, a0, a1)
                }
            }
          }
        }

      }

    }
  }
}
