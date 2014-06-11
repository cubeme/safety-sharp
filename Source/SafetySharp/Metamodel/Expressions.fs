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

namespace SafetySharp.Metamodel

/// Represents the operator in an unary expression.
type UnaryOperator =
    | Minus
    | LogicalNot

/// Represents the operator in a binary expression.
type BinaryOperator =
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

/// Represents side-effect free expressions within a model.
type Expression =
    /// Represents a Boolean literal, that is, either <c>true</c> or <c>false</c>.
    | BooleanLiteral of Value : bool

    /// Represents an integer value.
    | IntegerLiteral of Value : int

    /// Represents a decimal value.
    | DecimalLiteral of Value : decimal

    /// Represents the application of an unary operator to an expression.
    | UnaryExpression of Operand : Expression * Operator : UnaryOperator

    /// Represents the application of a binary operator to two subexpressions.
    | BinaryExpression of LeftExpression : Expression * Operator : BinaryOperator * RightExpression : Expression

    /// Represents a field access, either for reading or writing.
    | FieldAccessExpression of Field : FieldSymbol