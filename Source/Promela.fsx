// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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


// Not exactly the complete Promela-Syntax, just a subset and modified to be
// able to work with it conveniently.

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading

#load "Generator.fsx"
open Generator



let outputFile = "SafetySharp/Modelchecking/Promela/Promela.Generated.cs"
let elements = [
    {
        Name = "SafetySharp.Modelchecking.Promela"
        Classes =
        [
            {
                Name = "Identifier"
                Base = "PromelaElement"
                IsAbstract = false
                Properties =
                [
                    { 
                        Name = "Name"
                        Type = "string"
                        CollectionType = Generator.Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The name of the identifier."
                    }
                ]
            }
        ]
    }    
    {
        Name = "SafetySharp.Modelchecking.Promela.Expressions"
        Classes = 
        [
            {   
                Name = "Expression"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "StateVariableExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Variable"
                        Type = "StateVariableDeclaration"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The slot of the state variable."
                    }
                ]
            }
            {
                Name = "ConstExpression"
                Base = "Expression"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "BooleanLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "bool"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The Boolean value of the expression."
                    }
                ]
            }
            {
                Name = "BooleanLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "bool"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The Boolean value of the expression."
                    }
                ]
            }
            {
                Name = "SkipLiteral" //Convenience and generated code get prettier. Is equivalent to Boolean Literal True
                Base = "ConstExpression"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "BinaryExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                    }
                    {
                        Name = "Operator"
                        Type = "BinaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                    }
                    {
                        Name = "Right"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                    }
                ]
            }            
            {   
                Name = "UnaryExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                    }
                    {
                        Name = "Operator"
                        Type = "UnaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                    }
                ]
            }
        ]
    }
]

generateCode {
    Elements = elements
    OutputFile = outputFile
    BaseClass = "PromelaElement"
    VisitorName = "PromelaVisitor"
    RewriterName = "PromelaRewriter"
    VisitorNamespace = "SafetySharp.Modelchecking.Promela"
}


(*
(Nearly) Complete Ast of Promela in F#-Notation
see http://spinroot.com/spin/Man/grammar.html

// Promela accepts two different statement separators: an arrow `->'and the semicolon `;'. The two statement separators are equivalent

type Unarop =
    | Tilde // ~
    | Neg   // -
    | Not   // !

type Andor =
    | And  // &&
    | Or   // ||
    
type Binarop =
    | Add  // +
    | Min  // -
    | Mul  // *
    | Div  // /
    | Mod  // %
    | BAnd // & (Bitwise And)
    | Xor  // ^
    | BOr  // | (Bitwise Or)
    | Gt   // >
    | Lt   // >
    | Ge   // >=
    | Le   // <=
    | Eq   // ==
    | Neq  // !=
    | Bls  // << (Bitwise left shift)
    | Brs  // >> (Bitwise left shift)
    | Andor of Andor // &&, ||

type Const =
    | True  // is a synonym of the constant value one (1)
    | False // is a synonym of the constant value zero (0)
    | Skip  //is translated by the Spin lexical analyzer into the constant value one (1)
    | Number of int32

// varref	: name [ '[' any_expr ']' ] [ '.' varref ]
type Varref =
    | Varref of string * (AnyExpr option) * (Varref option)
        
// any_expr: '(' any_expr ')' ...
and AnyExpr =
    | BinaryExpr of AnyExpr * Binarop * AnyExpr
    | UnaryExpr of Unarop * AnyExpr
    | IfThenElse of AnyExpr * AnyExpr * AnyExpr // Meaning extracted from spin.yacc Zeile 714 (SPIN 6.2.5)
    | Varref of Varref
    | Const of Const

// expr	: any_expr ...
type Expr =
    | AnyExpr of AnyExpr
    | ExprAndOrExpr of Expr * Andor * Expr
//    | ChanPoll of

type Visible =
    | Hidden
    | Show

type Typename =
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
type Ivar =
    | Ivar  of string * (int32 option) * (AnyExpr option)

// one_decl: [ visible ] typename  ivar [',' ivar ] *
type OneDecl =
     | OneDecl of (Visible option) * Typename * (Ivar list)

// decl_lst: one_decl [ ';' one_decl ] *
type DeclLst = 
     DeclLst of (OneDecl list)

// assign  : varref '=' any_expr	/* standard assignment */
type Assign =
    | AssignExpr of Varref * AnyExpr
    | Incr of Varref
    | Decr of Varref
    
// range	: varref ':' expr '..' expr
type Range =
    | Range of Varref * Expr * Expr

// step    : stmnt	[ UNLESS stmnt ]
//          | decl_lst
type Step = 
    | StmntStep of Stmnt * (Stmnt option)
    | DeclListStep of DeclLst

// sequence: step [ ';' step ] *
and Sequence = 
    | Sequence of Step list

// options : ':' ':' sequence [ ':' ':' sequence ] *
and Options = 
    | Options of Sequence list

// stmnt	: IF options FI		/* selection */
and Stmnt =
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

type Priority = Int of int32 //Standard is 1

// init	: INIT [ priority ] '{' sequence '}'
type Init =
    | Init of (Priority option) * Sequence

// active  : ACTIVE [ '[' const ']' ]	/* instantiation */
type Active =
    | Active of (Const option)

// enabler : PROVIDED '(' expr ')'	/* execution constraint */
type Enabler = 
    | Expr of Expr

// proctype: [ active ] PROCTYPE name '(' [ decl_lst ]')'
// 	         [ priority ] [ enabler ] '{' sequence '}'
type Proctype =
    | Proctype of (Active option) * string * ( DeclLst option) * (Priority option) *  (Enabler option) * Sequence

type Module =
    | ProcTypeModule of Proctype
    | InitModule of Init
    | GlobalVarsAndChans of DeclLst
    
type Spec =
    | Spec of Module list


*)