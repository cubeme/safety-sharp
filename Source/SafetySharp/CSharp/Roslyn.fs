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
    /// Tries to cast the given syntax node to the parameter type expected by the projection and returns the projected value.
    let private projectNode (node : SyntaxNode) projection =
        match node with
        | :? 'a as node -> Some <| projection node
        | _ -> None

    /// Matches a literal expression.
    let (|LiteralExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (literal : LiteralExpressionSyntax) -> (literal.Token.CSharpKind (), literal.Token.Value)

    /// Matches a literal expression.
    let (|IdentifierName|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (identifier : IdentifierNameSyntax) -> identifier

    /// Matches a parenthesized expression.
    let (|ParenthesizedExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : ParenthesizedExpressionSyntax) -> expression.Expression

    /// Matches an unary expression.
    let (|UnaryExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : PrefixUnaryExpressionSyntax) -> (expression.Operand, expression.CSharpKind ())

    /// Matches a binary expression.
    let (|BinaryExpression|_|) (expression : ExpressionSyntax) =
        projectNode expression <| fun (expression : BinaryExpressionSyntax) -> (expression.Left, expression.CSharpKind (), expression.Right)

    /// Matches an assignment expression.
    let (|AssignmentExpression|_|) (expression : ExpressionSyntax) =
        match projectNode expression <| fun (expression : BinaryExpressionSyntax) -> (expression.Left, expression.CSharpKind (), expression.Right) with
        | Some (left, operator, right) when operator = SyntaxKind.SimpleAssignmentExpression ->
            Some (left, right)
        | _ -> None

    /// Matches an empty statement.
    let (|EmptyStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : EmptyStatementSyntax) -> ()

    /// Matches a block statement.
    let (|BlockStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : BlockSyntax) -> statement.Statements

    /// Matches an expression statement.
    let (|ExpressionStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : ExpressionStatementSyntax) -> statement.Expression

    /// Matches a return statement.
    let (|ReturnStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : ReturnStatementSyntax) -> 
            match statement.Expression with null -> None | expression -> Some expression

    /// Matches an if-then-else statement.
    let (|IfStatement|_|) (statement : StatementSyntax) =
        projectNode statement <| fun (statement : IfStatementSyntax) -> 
            let elseStatement = match statement.Else with null -> None | elseClause -> Some elseClause.Statement
            (statement.Condition, statement.Statement, elseStatement)
