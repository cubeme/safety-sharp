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

namespace SafetySharp.CSharp

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

module internal Roslyn =
    let private projectNode (node : SyntaxNode) projection =
        match node with
        | :? 'a as node -> Some <| projection node
        | _ -> None

    let (|LiteralExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (literal : LiteralExpressionSyntax) -> (literal.Token.CSharpKind (), literal.Token.Value)

    let (|IdentifierName|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (identifier : IdentifierNameSyntax) -> identifier

    let (|ParenthesizedExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : ParenthesizedExpressionSyntax) -> expression.Expression

    let (|UnaryExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : PrefixUnaryExpressionSyntax) -> (expression.Operand, expression.CSharpKind ())

    let (|BinaryExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : BinaryExpressionSyntax) -> (expression.Left, expression.CSharpKind (), expression.Right)

    let (|AssignmentExpression|_|) (expression : ExpressionSyntax) =
        match expression with
        | BinaryExpression (left, operator, right) when operator = SyntaxKind.SimpleAssignmentExpression -> Some (left, right)
        | _ -> None

    let (|InvocationExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : InvocationExpressionSyntax) -> expression

    let (|EmptyStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : EmptyStatementSyntax) -> ()

    let (|BlockStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : BlockSyntax) -> statement.Statements

    let (|ExpressionStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : ExpressionStatementSyntax) -> statement.Expression

    let (|ReturnStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : ReturnStatementSyntax) -> if statement.Expression = null then None else Some statement.Expression

    let (|IfStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : IfStatementSyntax) -> 
            let elseStatement = if statement.Else = null then None else Some statement.Else.Statement
            (statement.Condition, statement.Statement, elseStatement)
