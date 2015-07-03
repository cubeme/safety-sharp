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

namespace SafetySharp.Models

module internal Sam =

    /// Represents the operator in an unary expression.
    type internal UOp =
        | Not

    /// Represents the operator in a binary expression.
    type internal BOp =
        // Arithmetic operators
        | Add
        | Subtract
        | Multiply
        | Divide
        | Modulo
    
        // Logical operators
        | And
        | Or
        | Implies
    
        // Equality operators
        | Equals
        | NotEquals
    
        // Comparison operators
        | Less
        | LessEqual
        | Greater
        | GreaterEqual

    type internal Var =
        | Var of string
        
    type internal OverflowBehavior = SafetySharp.Models.Scm.OverflowBehavior

    type internal Val = 
        /// Represents a Boolean literal, that is, either <c>true</c> or <c>false</c>.
        | BoolVal of bool
        /// Represents a number value.
        | NumbVal of Value : bigint
        
        | RealVal of double

        | ProbVal of double
                
    [<RequireQualifiedAccessAttribute>]
    type internal Element =
        | GlobalVar of Var
        | LocalVar of Var

    /// Represents side-effect free expressions within a SAM model.
    type internal Expr =
        /// Represents a literal
        | Literal of Val

        /// Represents the application of an unary operator to an expression.
        | UExpr of Operand : Expr * Operator : UOp

        /// Represents the application of a binary operator to two subexpressions.
        | BExpr of LeftExpression : Expr * Operator : BOp * RightExpression : Expr
        
        /// Represents the if then else operator ("the" ternary operator
        | IfThenElseExpr of GuardExpr : Expr * ThenExpr : Expr * ElseExpr : Expr
    
        /// Represents a read operation of a variable.
        | Read of Element : Element

        /// Represents a read operation of the previous value of a variable.
        | ReadOld of Element : Element

    type internal Clause = {
        Guard:Expr;
        Statement:Stm;
    }

    /// Represents statements contained within method bodies.
    and internal Stm =
        /// Represents a list of statements that are executed sequentially.
        | Block of Statements: Stm list
    
        /// Represents a guarded command statement. The body of at most one clause of the guarded command is
        /// executed. For a body to be executed, its guard must evaluate to true. If multiple guards hold, one
        /// clause is chosen nondeterministically.
        | Choice of Clauses : Clause list

        | Stochastic of (Expr * Stm) list //Expr must be of type ProbVal

        /// Represents the assignment of a variable.
        | Write of Element:Element * Expression:Expr

    type internal Type =
        | BoolType
        | IntType // for local variables, which get inlined
        | RealType // for local variables, which get inlined
        | RangedIntType of From:int * To:int * Overflow:OverflowBehavior
        | RangedRealType of From:double  * To:double * Overflow:OverflowBehavior
            with
                member this.getDefaultValue : Val =
                    match this with
                        | BoolType -> Val.BoolVal(false)
                        | IntType  -> Val.NumbVal(bigint 0)
                        | RealType  -> Val.RealVal(0.0)
                        | RangedIntType (from:int,_,_) -> Val.NumbVal(bigint from)
                        | RangedRealType (from:double,_,_) -> Val.RealVal(from)


    type internal GlobalVarDecl = {
        Var : Var
        Type : Type
        Init : Val list //Initial values are expected to be in range of type
    }


    type internal LocalVarDecl = {
        Var : Var
        Type : Type
    }

    type internal Traceable =
        | Traceable of Var
        | TraceableRemoved of Reason:string
            with
                override traceable.ToString() =
                    match traceable with
                        | Traceable(Var(name)) ->
                            sprintf "global variable '%s'" name
                        | TraceableRemoved(reason) ->
                            sprintf "removed (reason:%s)" (reason)
                    

    type internal Pgm = {
        Globals : GlobalVarDecl list
        Locals : LocalVarDecl list
        Body : Stm
    }