// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace SafetySharp.Analysis.Modelchecking.PromelaSpin
(*

Grammar: http://spinroot.com/spin/Man/grammar.html
Basic Manual: http://spinroot.com/spin/Man/Manual.html

*)

// Names of types from: http://spinroot.com/spin/Man/grammar.html
// Promela accepts two different statement separators: an arrow `->'and the semicolon `;'. The two statement separators are equival

type internal Const =
    | True  // is a synonym of the constant value one (1)
    | False // is a synonym of the constant value zero (0)
    | Skip  //is translated by the Spin lexical analyzer into the constant value one (1)
    | Number of int32

// varref	: name [ '[' any_expr ']' ] [ '.' varref ]
type internal Varref =
    | Varref of string * (AnyExpr option) * (Varref option)
        
// any_expr: '(' any_expr ')' ...
and internal AnyExpr =
    | BinaryExpr of AnyExpr * Binarop * AnyExpr
    | UnaryExpr of Unarop * AnyExpr
    | IfThenElse of AnyExpr * AnyExpr * AnyExpr // Meaning concluded from spin.yacc line 714 (SPIN 6.2.5)
    | Varref of Varref
    | Const of Const

// expr	: any_expr ...
type internal Expr =
    | AnyExpr of AnyExpr
    | ExprAndOrExpr of Expr * Andor * Expr
//    | ChanPoll of

type internal Visible =
    | Hidden
    | Show

type internal Typename =
    | Bit
    | Bool
    | Byte
    | Short
    | Int
    | Mtype
    | Chan
    // | Pid (this one is not mentioned in the short grammar of the SPIN website. It is equivalent to byte. "Skip" (equivalent to the const "1") is similar but mentioned in the syntax. Perhaps we should introduce it explicitly and deviate from the webpage's grammar.
    //| Uname TODO: Userdefined...

// ivar    : name [ '[' const ']' ] [ '=' any_expr | '=' ch_init ]
type internal Ivar =
    | Ivar  of string * (int32 option) * (AnyExpr option)

// one_decl: [ visible ] typename  ivar [',' ivar ] *
type internal OneDecl =
     | OneDecl of (Visible option) * Typename * (Ivar list)

// decl_lst: one_decl [ ';' one_decl ] *
type internal DeclLst = 
     DeclLst of (OneDecl list)

// assign  : varref '=' any_expr	/* standard assignment */
type internal Assign =
    | AssignExpr of Varref * AnyExpr
    | Incr of Varref
    | Decr of Varref
    
// range	: varref ':' expr '..' expr
type internal Range =
    | Range of Varref * Expr * Expr

// step    : stmnt	[ UNLESS stmnt ]
//          | decl_lst
type internal Step = 
    | StmntStep of Stmnt * (Stmnt option)
    | DeclListStep of DeclLst

// sequence: step [ ';' step ] *
and internal Sequence = 
    | Sequence of Step list

// options : ':' ':' sequence [ ':' ':' sequence ] *
and internal Options = 
    | Options of Sequence list

// stmnt	: IF options FI		/* selection */
and internal Stmnt =
    | IfStmnt of Options
    | DoStmnt of Options
    | ForStmnt of Range * Sequence
    | AtomicStmnt of Sequence
    | DStepStmnt of Sequence
    | SelectStmnt of Range
    | SequenceStmnt of Sequence
    | AssignStmnt of Assign
    | ElseStmnt // used inside options (if no other guard of the available options is true)
    | GotoStmnt of string
    | LabeledStmnt of string * Stmnt // as destination of goto
    | AssertStmnt of Expr 
    | ExprStmnt of Expr

type internal Priority = Int of int32 //Standard is 1

// init	: INIT [ priority ] '{' sequence '}'
type internal Init =
    | Init of (Priority option) * Sequence

// active  : ACTIVE [ '[' const ']' ]	/* instantiation */
type internal Active =
    | Active of (Const option)

// enabler : PROVIDED '(' expr ')'	/* execution constraint */
type internal Enabler = 
    | Expr of Expr

// proctype: [ active ] PROCTYPE name '(' [ decl_lst ]')'
// 	         [ priority ] [ enabler ] '{' sequence '}'
type internal Proctype =
    | Proctype of (Active option) * string * ( DeclLst option) * (Priority option) *  (Enabler option) * Sequence

type internal Module =
    | ProcTypeModule of Proctype
    | InitModule of Init
    | GlobalVarsAndChans of DeclLst
    

[<RequireQualifiedAccessAttribute>]
type internal LtlExpr =
    | BinaryExpr of LtlExpr * Binarop * LtlExpr
    | UnaryExpr of Unarop * LtlExpr
    | Varref of Varref
    | Const of Const
    | BinaryLtlExpr of LtlExpr * BinaryLtlOperator * LtlExpr
    | UnaryLtlExpr of LtlExpr * UnaryLtlOperator

type internal Spec = {
    Code : Module list;
    Formulas : LtlExpr list;
}