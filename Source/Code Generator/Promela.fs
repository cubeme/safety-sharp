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
// We do not allow to declare variables as freely as in Promela. We only allow
// local variables inside a proctype. Thus there is no need to distinguish
// between declarations (which can appear outside of proctypes) and other
// statements. This simplify the Ast radically (no step) and makes it easier to
// understand. Also we only allow one declaration per Statement.

module PromelaGenerator

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading
open Generator

let elements = [
    {
        // proctype: [ active ] PROCTYPE name '(' [ decl_lst ]')'
        // 	         [ priority ] [ enabler ] '{' sequence '}'
        Name = "SafetySharp.Modelchecking.Promela"
        Classes =
        [
            {   
                Name = "Proctype"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "IsActive"
                        Type = "bool"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "If true then Proctype gets automatically executed at startup."
                        CanBeNull = false
                    }
                    {
                        Name = "Name"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the Proctype."
                        CanBeNull = false
                    }
                    {
                        Name = "Code"
                        Type = "Statement"
                        CollectionType = Array
                        Validation = None
                        Comment = "A list of statements with the code of the Proctype."
                        CanBeNull = false
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
                Base = "PromelaElement"
                IsAbstract = true
                Properties = []
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
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "NumberLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The Boolean value of the expression."
                        CanBeNull = false
                    }
                ]
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
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "PromelaBinaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                        CanBeNull = false
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
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "PromelaUnaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                //The expression which references a variable.
                Name = "VariableReferenceExpression" // varref	: name [ '[' any_expr ']' ] [ '.' varref ]
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the identifier which references a variable."
                        CanBeNull = false
                    }
                    {
                        Name = "Index"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Identifier references an array. This is the index of a specific element in this array."
                        CanBeNull = true
                    }
                    {
                        Name = "Member"
                        Type = "VariableReferenceExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Identifier (and maybe the Index) reference a struct. This references a specific member in this struct."
                        CanBeNull = true
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Modelchecking.Promela.Statements"
        Classes = 
        [
            {   
                Name = "Statement"
                Base = "PromelaElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "BlockStatement"
                Base = "Statement"
                IsAbstract = true
                Properties = 
                [
                    {
                        Name = "Statements"
                        Type = "Statement"
                        CollectionType = Array
                        Validation = None
                        Comment = "A list of statements."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "SimpleBlockStatement"
                Base = "BlockStatement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "AtomicBlockStatement"
                Base = "BlockStatement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "DStepBlockStatement"
                Base = "BlockStatement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "ReturnStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression that should be evaluated and returned."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ExpressionStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression that should be evaluated."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "SkipStatement" //Convenience and generated code gets prettier. In Promela it is equivalent to a ExpressionStatement with the Boolean Literal True
                Base = "Statement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "GuardedCommandRepetitionStatement"  //do :: od
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Clauses"
                        Type = "GuardedCommandClause"
                        CollectionType = Array
                        Validation = None
                        Comment = "The clauses of the guarded command, one of which is chosen nondeterministically during execution if multiple guards hold."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "GuardedCommandSelectionStatement" //if :: fi
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Clauses"
                        Type = "GuardedCommandClause"
                        CollectionType = Array
                        Validation = None
                        Comment = "The clauses of the guarded command, one of which is chosen nondeterministically during execution if multiple guards hold."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "GuardedCommandClause"
                Base = "PromelaElement"
                IsAbstract = true
                Properties = []
            }          
            {   
                Name = "GuardedCommandExpressionClause"
                Base = "GuardedCommandClause"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Guard"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The guard of the clause that determines whether the statement can be executed."
                        CanBeNull = false
                    }
                    {
                        Name = "Statement"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The statement of the clause that can only be executed if the guard holds."
                        CanBeNull = false
                    }
                ]
            }          
            {   
                Name = "GuardedCommandElseClause"
                Base = "GuardedCommandClause"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Statement"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The statement of the clause that can only be executed if no other clause holds."
                        CanBeNull = false
                    }
                ]
            }          
            {   
                Name = "AssignmentStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "VariableReferenceExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The reference to the variable on the left-hand side of the assignment operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the assignment operator."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "DeclarationStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Type"
                        Type = "PromelaTypeName"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The type of the declared variable."
                        CanBeNull = false
                    }
                    {
                        Name = "Identifier"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the declared variable."
                        CanBeNull = false
                    }
                    {
                        Name = "ArraySize"
                        Type = "Int32"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The size of the array, if declared variable is an array. Otherwise 0."
                        CanBeNull = false
                    }
                    {
                        Name = "InitialValue"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "An expression, which determines the initial value of the declared variable."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }
]

let Generate outputFile =
    generateCode {
        Elements = elements
        OutputFile = outputFile
        BaseClass = "PromelaElement"
        VisitorName = "PromelaVisitor"
        RewriterName = "PromelaRewriter"
        Namespace = "SafetySharp.Modelchecking.Promela"
        Public = false
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