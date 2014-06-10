namespace SafetySharp.CSharp

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

module Roslyn =
    /// Matches a literal expression.
    let (|LiteralExpression|_|) (expression : ExpressionSyntax) =
        match expression with
        | :? LiteralExpressionSyntax as literal -> 
            Some (literal.Token.CSharpKind(), literal.Token.Value)
        | _ ->
            None

    /// Matches a literal expression.
    let (|IdentifierName|_|) (expression : ExpressionSyntax) =
        match expression with
        | :? IdentifierNameSyntax as identifier -> 
            Some identifier
        | _ ->
            None

    /// Matches a parenthesized expression.
    let (|ParenthesizedExpression|_|) (expression : ExpressionSyntax) =
        match expression with
        | :? ParenthesizedExpressionSyntax as expression -> 
            Some expression.Expression
        | _ ->
            None

    /// Matches an unary expression.
    let (|UnaryExpression|_|) (expression : ExpressionSyntax) =
        match expression with
        | :? PrefixUnaryExpressionSyntax as expression -> 
            Some (expression.Operand, expression.CSharpKind())
        | _ ->
            None

    /// Matches a binary expression.
    let (|BinaryExpression|_|) (expression : ExpressionSyntax) =
        match expression with
        | :? BinaryExpressionSyntax as expression -> 
            Some (expression.Left, expression.CSharpKind(), expression.Right)
        | _ ->
            None