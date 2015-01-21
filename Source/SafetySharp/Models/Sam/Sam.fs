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

namespace SafetySharp.Models.Sam

/// Represents the operator in an unary expression.
type internal UOp =
    | Not

/// Represents the operator in a binary expression. (same as SafetySharp.Internal.Metamodel.UnaryOperatorBinaryOperator)
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
        
type internal Val = 
    /// Represents a Boolean literal, that is, either <c>true</c> or <c>false</c>.
    | BoolVal of bool
    /// Represents a number value.
    | NumbVal of Value : bigint

/// Represents side-effect free expressions within a FIL model. (not the same as SafetySharp.Internal.Metamodel.Expression)
type internal Expr =
    /// Represents a literal
    | Literal of Val

    /// Represents the application of an unary operator to an expression.
    | UExpr of Operand : Expr * Operator : UOp

    /// Represents the application of a binary operator to two subexpressions.
    | BExpr of LeftExpression : Expr * Operator : BOp * RightExpression : Expr
    
    /// Represents a read operation of a variable.
    | Read of Variable : Var

    /// Represents a read operation of the previous value of a variable.
    | ReadOld of Variable : Var

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

    /// Represents the assignment of a variable.
    | Write of Variable:Var * Expression:Expr

type internal Type =
    | BoolType
    | IntType

type internal GlobalVarDecl = {
    Var : Var
    Type : Type
    Init : Val list 
}


type internal LocalVarDecl = {
    Var : Var
    Type : Type
}

type internal Pgm = {
    Globals : GlobalVarDecl list
    Locals : LocalVarDecl list
    Body : Stm
}