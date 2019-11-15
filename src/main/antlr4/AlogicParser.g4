////////////////////////////////////////////////////////////////////////////////
// Argon Design Ltd. Project P8009 Alogic
// Copyright (c) 2017-2019 Argon Design Ltd. All rights reserved.
//
// This file is covered by the BSD (with attribution) license.
// See the LICENSE file for the precise wording of the license.
//
// Module: Alogic Compiler
// Author: Peter de Rivaz/Geza Lore
//
// DESCRIPTION:
//
// Antlr4 parser grammar for Alogic
////////////////////////////////////////////////////////////////////////////////

parser grammar AlogicParser;

options {
  tokenVocab = AlogicLexer;
}

////////////////////////////////////////////////////////////////////////////////
// Start rule for whole source file
////////////////////////////////////////////////////////////////////////////////

root : riz* EOF ;

////////////////////////////////////////////////////////////////////////////////
// Identifiers
////////////////////////////////////////////////////////////////////////////////

ident : IDENTIFIER ('#' '[' expr (',' expr)* ']')? ;

////////////////////////////////////////////////////////////////////////////////
// Declarations
////////////////////////////////////////////////////////////////////////////////

decl : attrs? declbase ;

attrs : '(*' attr (',' attr)* '*)' ;
attr : IDENTIFIER ('=' expr)? ;

declbase
  : expr ident ('=' init=expr)? ';'                     # DeclVar
  | 'in' fct? expr ident ';'                            # DeclIn
  | 'out' fct? stt? expr ident ('=' init=expr)? ';'     # DeclOut
  | 'pipeline' expr ident ';'                           # DeclPipeline
  | 'param' expr IDENTIFIER ('=' init=expr)?  ';'       # DeclParam
  | 'const' expr IDENTIFIER '=' expr  ';'               # DeclConst
  | expr ident '[' expr ']' ';'                         # DeclArr
  | 'sram' (wire='wire')? expr ident '[' expr ']' ';'   # DeclSram
  | 'typedef' expr ident ';'                            # DeclType
  | entity_keyword ident '{' ent* '}'                   # DeclEntity
  | 'struct' ident '{' rec* '}'                         # DeclRecord
  | ident '=' 'new' expr ';'                            # DeclInstance
  | 'new' entity_keyword ident '{' ent* '}'             # DeclSingleton
  | expr ident '(' ')' '{' stmt* '}'                    # DeclFunc
  ;

fct
  : 'sync'        # FCTSync
  | SYNC_READY    # FCTSyncReady
  | SYNC_ACCEPT   # FCTSyncAccept
  ;

stt
  : 'wire'                                      # STTWire
  | (slices+=('bubble' | 'fslice' | 'bslice'))+ # STTSlices
  ;

entity_keyword
  : 'fsm'
  | 'network'
  | 'verbatim' 'entity'
  ;

////////////////////////////////////////////////////////////////////////////////
// Gen constructs
////////////////////////////////////////////////////////////////////////////////

gen : 'gen' generate ;

generate
  : 'if' '(' thenCond=expr ')' '{' thenItems=genitems '}'
    ('else' 'if' '(' elifCond+=expr ')' '{' elifItems+=genitems '}')*
    ('else' '{' elseItems=genitems '}')?                                    # GenIf
  | 'for' '(' ginits ';' expr ';' lsteps ')' '{' genitems '}'               # GenFor
  | 'for' '(' expr IDENTIFIER op=('<' | '<=')  expr ')' '{' genitems '}'    # GenRange
  ;

genitems : genitem* ;
genitem
  : gen     # GenItemGen
  | decl    # GenItemDecl
  | stmt    # GenItemStmt
  | kase    # GenItemCase
  | ent     # GenItemEnt
  | rec     # GenItemRec
  ;

ginits : ginit (',' ginit)* ;
ginit : expr IDENTIFIER point='=' expr ;

////////////////////////////////////////////////////////////////////////////////
// File contents
////////////////////////////////////////////////////////////////////////////////


riz
  : decl    # RizDecl
  ;

////////////////////////////////////////////////////////////////////////////////
// Entity contents
////////////////////////////////////////////////////////////////////////////////

ent
  : decl                                                # EntDecl
  | gen                                                 # EntGen
  | lhs=expr point='->' rhs+=expr (',' rhs+=expr)* ';'  # EntConnect
  | 'fence' '{' stmt* '}'                               # EntFenceBlock
  | 'verbatim' IDENTIFIER VERBATIM_BODY                 # EntVerbatimBlock
  ;

////////////////////////////////////////////////////////////////////////////////
// Record contents
////////////////////////////////////////////////////////////////////////////////

rec
  : decl    # RecDecl
  | gen     # RecGen
  ;

////////////////////////////////////////////////////////////////////////////////
// Statements
////////////////////////////////////////////////////////////////////////////////

stmt
  : decl                                                        # StmtDecl
  | gen                                                         # StmtGen
  | '{' stmt* '}'                                               # StmtBlock
  | 'if' '(' expr ')' thenStmt=stmt ('else' elseStmt=stmt)?     # StmtIf
  | 'case' '(' expr ')' '{' kase* '}'                           # StmtCase
  | 'loop' '{' stmt* '}'                                        # StmtLoop
  | 'do' '{' stmt* '}' 'while' '(' expr ')' ';'                 # StmtDo
  | 'while' '(' expr ')' '{' stmt* '}'                          # StmtWhile
  | 'for' '(' linits?  ';' expr? ';' lsteps? ')' '{' stmt* '}'  # StmtFor
  | 'let' '(' linits ')' stmt                                   # StmtLet
  | 'fence' ';'                                                 # StmtFence
  | 'break' ';'                                                 # StmtBreak
  | 'continue' ';'                                              # StmtContinue
  | 'goto' ident ';'                                            # StmtGoto
  | 'return' ';'                                                # StmtReturn
  | expr point='=' expr ';'                                     # StmtAssign
  | expr ASSIGNOP expr ';'                                      # StmtUpdate
  | expr op=('++'|'--') ';'                                     # StmtPost
  | expr ';'                                                    # StmtExpr
  ;

kase
  : gen                         # CaseGen
  | expr (',' expr)* ':' stmt   # CaseRegular
  | 'default' ':' stmt          # CaseDefault
  ;

linits : linit (',' linit)* ;
linit
  : expr point='=' expr             # LoopInitAssign
  | expr IDENTIFIER point='=' expr  # LoopInitDecl
  ;

lsteps : lstep (',' lstep)* ;
lstep
  : expr point='=' expr # LoopStepAssign
  | expr ASSIGNOP expr  # LoopStepUpdate
  | expr op=('++'|'--') # LoopStepPost
  ;

////////////////////////////////////////////////////////////////////////////////
// Expressions
////////////////////////////////////////////////////////////////////////////////

expr
  : '(' expr ')'                                                # ExprBracket
  // Literals
  | 'true'                                                      # ExprLitTrue
  | 'false'                                                     # ExprLitFalse
  | sign=('+' | '-')? SIZEDINT                                  # ExprLitSizedInt
  | sign=('+' | '-')? UNSIZEDINT                                # ExprLitUnsizedInt
  | STRING                                                      # ExprLitString
  // Primitive types
  | 'bool'                                                      # ExprTypeBool
  | INTTYPE                                                     # ExprTypeSInt
  | UINTTYPE                                                    # ExprTypeUInt
  | 'int'                                                       # ExprTypeSNum
  | 'uint'                                                      # ExprTypeUNum
  | 'void'                                                      # ExprTypeVoid
  // Names
  | ident                                                       # ExprIdent
  | ATID                                                        # ExprAtid
  | DOLLARID                                                    # ExprDollarid
  // Call
  | expr '(' args? ')'                                          # ExprCall
  // Index/Slice
  | expr '[' idx=expr ']'                                       # ExprIndex
  | expr '[' lidx=expr op=(':' | '-:' | '+:') ridx=expr ']'     # ExprSlice
  // Select
  | expr '.' ident                                              # ExprSelect
  // Operators
  | op=('+' | '-' | '~' | '!' | '&' | '|' | '^' | '\'' ) expr   # ExprUnary
  | expr op=('*' | '/' | '%') expr                              # ExprBinary
  | expr op=('+' | '-') expr                                    # ExprBinary
  | expr op=('<<' | '>>' | '>>>' | '<<<' ) expr                 # ExprBinary
  | expr op=('>' | '>=' | '<' | '<=') expr                      # ExprBinary
  | expr op=('==' | '!=') expr                                  # ExprBinary
  | expr op='&' expr                                            # ExprBinary
  | expr op='^' expr                                            # ExprBinary
  | expr op='|' expr                                            # ExprBinary
  | expr op='&&' expr                                           # ExprBinary
  | expr op='||' expr                                           # ExprBinary
  |<assoc=right> expr op='?' expr ':' expr                      # ExprTernary
  | '{' expr s='{' expr (',' expr)* e='}' '}'                   # ExprRep
  | '{' expr (',' expr)* '}'                                    # ExprCat
  ;

args : arg (',' arg)* ;
arg
  : IDENTIFIER point='=' expr   # ArgNamed
  | expr                        # ArgPositional
  ;