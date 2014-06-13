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

namespace SafetySharp.CSharp.Transformation

open System.Collections.Immutable
open SafetySharp.Metamodel
open SafetySharp.CSharp.Roslyn
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

module ExpressionTransformation =

    /// Transforms a C# expression to a metamodel expression.
    let Transform (symbolResolver : SymbolResolver) (semanticModel : SemanticModel) (expression : ExpressionSyntax) =
        let rec transform = function
        | LiteralExpression (kind, value) ->
            match kind with
            | SyntaxKind.TrueKeyword -> BooleanLiteral true
            | SyntaxKind.FalseKeyword -> BooleanLiteral false
            | SyntaxKind.NumericLiteralToken ->
                match value with
                | :? int as value -> IntegerLiteral value
                | :? decimal as value -> DecimalLiteral value
                | _ -> sprintf "Numeric literals of type '%A' are not supported." kind |> invalidOp
            | _ -> sprintf "Unsupported C# literal: '%A'" kind |> invalidOp

        | IdentifierName identifier ->
            let symbolInfo = semanticModel.GetSymbolInfo identifier
            let symbol = symbolInfo.Symbol;

            match symbol with
            | :? IFieldSymbol as field -> symbolResolver.ResolveField field |> FieldAccessExpression
            | _ -> sprintf "Unable to determine symbol for identifier '{%A}'." identifier |> invalidOp

        | ParenthesizedExpression expression ->
            transform expression

        | UnaryExpression (operand, operator) ->
            match operator with
            | SyntaxKind.UnaryPlusExpression -> transform operand
            | SyntaxKind.UnaryMinusExpression -> UnaryExpression (transform operand, UnaryOperator.Minus)
            | SyntaxKind.LogicalNotExpression -> UnaryExpression (transform operand, UnaryOperator.LogicalNot)
            | _ -> sprintf "Unsupported unary C# operator: '%A'." operator |> invalidOp

        | BinaryExpression (left, operator, right) ->
            let operator = 
                match operator with
                | SyntaxKind.AddExpression -> BinaryOperator.Add;
                | SyntaxKind.SubtractExpression -> BinaryOperator.Subtract;
                | SyntaxKind.MultiplyExpression -> BinaryOperator.Multiply;
                | SyntaxKind.DivideExpression -> BinaryOperator.Divide;
                | SyntaxKind.ModuloExpression -> BinaryOperator.Modulo;
                | SyntaxKind.LogicalAndExpression -> BinaryOperator.LogicalAnd;
                | SyntaxKind.LogicalOrExpression -> BinaryOperator.LogicalOr;
                | SyntaxKind.EqualsExpression -> BinaryOperator.Equals;
                | SyntaxKind.NotEqualsExpression -> BinaryOperator.NotEquals;
                | SyntaxKind.LessThanExpression -> BinaryOperator.LessThan;
                | SyntaxKind.LessThanOrEqualExpression -> BinaryOperator.LessThanOrEqual;
                | SyntaxKind.GreaterThanExpression -> BinaryOperator.GreaterThan;
                | SyntaxKind.GreaterThanOrEqualExpression -> BinaryOperator.GreaterThanOrEqual;
                | _ -> sprintf "Unsupported binary C# operator: '%A'." operator |> invalidOp
            BinaryExpression (transform left, operator, transform right)

        | _ ->
            expression.CSharpKind () |> sprintf "Encountered an unexpected C# syntax node: '%A'." |> invalidOp

        transform expression
        