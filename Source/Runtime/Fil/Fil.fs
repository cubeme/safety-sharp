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

namespace SafetySharp.Internal.FIL

/// Represents the operator in an unary expression.
type internal UnaryOperator =
    | LogicalNot

/// Represents the operator in a binary expression. (same as SafetySharp.Internal.Metamodel.UnaryOperatorBinaryOperator)
type internal BinaryOperator =
    // Arithmetic operators
    | Add
    | Subtract
    | Multiply
    | Divide
    | Modulo
    
    // Logical operators
    | LogicalAnd
    | LogicalOr
    
    // Equality operators
    | Equals
    | NotEquals
    
    // Comparison operators
    | LessThan
    | LessThanOrEqual
    | GreaterThan
    | GreaterThanOrEqual

type internal Identifier =
    | Identifier of string

/// Represents side-effect free expressions within a FIL model. (not the same as SafetySharp.Internal.Metamodel.Expression)
type internal Expression =
    /// Represents a Boolean literal, that is, either <c>true</c> or <c>false</c>.
    | BooleanLiteral of Value : bool

    /// Represents a number value.
    | NumberLiteral of Value : bigint

    /// Represents the application of an unary operator to an expression.
    | UnaryExpression of Operand : Expression * Operator : UnaryOperator

    /// Represents the application of a binary operator to two subexpressions.
    | BinaryExpression of LeftExpression : Expression * Operator : BinaryOperator * RightExpression : Expression
    
    /// Represents a read operation of a variable.
    | ReadVariable of Variable : Identifier

    /// Represents a read operation of the previous value of a variable.
    | ReadVariablePrev of Variable : Identifier

type internal GuardedCommandClause =
    | GuardedCommandClause of Guard:Expression * Statement:Statement

/// Represents statements contained within method bodies.
and internal Statement =
    /// Represents the empty statement that does nothing.
    | EmptyStatement

    /// Represents a list of statements that are executed sequentially.
    | BlockStatement of Statements: Statement list
    
    /// Represents a guarded command statement. The body of at most one clause of the guarded command is
    /// executed. For a body to be executed, its guard must evaluate to true. If multiple guards hold, one
    /// clause is chosen nondeterministically.
    | GuardedCommandStatement of Clauses : GuardedCommandClause list

    /// Represents the assignment of a variable.
    | WriteVariable of Variable:Identifier * Expression:Expression