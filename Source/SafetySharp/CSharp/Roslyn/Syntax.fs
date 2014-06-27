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

namespace SafetySharp.CSharp.Roslyn

open System
open System.Linq
open System.Text
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities
open SafetySharp.Modeling

module Syntax =

    /// Removes all leading and trailing trivia from the syntax node.
    let RemoveTrivia (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithLeadingTrivia().WithTrailingTrivia ()

    /// Replaces the given leading and trailing trivia of the syntax node.
    let WithTrivia (leadingTrivia : SyntaxTriviaList) (trailingTrivia : SyntaxTriviaList) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithLeadingTrivia(leadingTrivia).WithTrailingTrivia trailingTrivia

    /// Replaces the syntax node's leading and trailing trivia with the trivia of the the given template syntax node.
    let WithTriviaFromNode (templateNode : SyntaxNode) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        nullArg templateNode "templateNode"
        syntaxNode.WithLeadingTrivia(templateNode.GetLeadingTrivia ()).WithTrailingTrivia (templateNode.GetTrailingTrivia ())

    /// Replaces the syntax node's leading and trailing trivia with the trivia of the the given syntax token.
    let WithTriviaFromToken (token : SyntaxToken) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithLeadingTrivia(token.LeadingTrivia).WithTrailingTrivia token.TrailingTrivia

    /// Replaces the syntax node's leading trivia with the trivia of the the given template syntax node.
    let WithLeadingTriviaFromNode (templateNode : SyntaxNode) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        nullArg templateNode "templateNode"
        syntaxNode.WithLeadingTrivia (templateNode.GetLeadingTrivia ())

    /// Replaces the syntax node's leading trivia with the trivia of the the given syntax token.
    let WithLeadingTriviaFromToken (token : SyntaxToken) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithLeadingTrivia token.LeadingTrivia

    /// Replaces the syntax node's trailing trivia with the trivia of the the given template syntax node.
    let WithTrailingTriviaFromNode (templateNode : SyntaxNode) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        nullArg templateNode "templateNode"
        syntaxNode.WithTrailingTrivia (templateNode.GetTrailingTrivia ())

    /// Replaces the syntax node's trailing trivia with the trivia of the the given syntax token.
    let WithTrailingTriviaFromToken (token : SyntaxToken) (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithTrailingTrivia token.TrailingTrivia

    /// Surrounds the syntax node with a single leading and trailing space.
    let WithLeadingAndTrailingSpace (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithLeadingTrivia(SyntaxFactory.Space).WithTrailingTrivia SyntaxFactory.Space

    /// Replaces the syntax node's leading trivia with a single white space.
    let WithLeadingSpace (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithLeadingTrivia SyntaxFactory.Space

    /// Replaces the syntax node's trailing trivia with a single white space.
    let WithTrailingSpace (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.WithTrailingTrivia SyntaxFactory.Space

    /// Normalizes all white space contained in the syntax node and its children.
    let NormalizeWhitespace (syntaxNode : #SyntaxNode) =
        nullArg syntaxNode "syntaxNode"
        syntaxNode.NormalizeWhitespace ()

    /// Creates a syntax token list containing the appropriate visibility modifier(s).
    let VisibilityModifier = function
        | Private -> 
            SyntaxFactory.TokenList (SyntaxFactory.Token SyntaxKind.PrivateKeyword)
        | Protected -> 
            SyntaxFactory.TokenList (SyntaxFactory.Token SyntaxKind.ProtectedKeyword)
        | Internal -> 
            SyntaxFactory.TokenList (SyntaxFactory.Token SyntaxKind.InternalKeyword)
        | ProtectedInternal -> 
            let protectedKeyword = SyntaxFactory.Token(SyntaxKind.ProtectedKeyword).WithTrailingTrivia SyntaxFactory.Space
            let internalKeyword = SyntaxFactory.Token SyntaxKind.InternalKeyword
            SyntaxFactory.TokenList (protectedKeyword, internalKeyword)
        | Public -> 
            SyntaxFactory.TokenList (SyntaxFactory.Token SyntaxKind.PublicKeyword)

    /// Creates a <see cref="AccessorDeclaration" /> of the given type with the given visibility.
    let Accessor accessorType visibility =
            let accessor = SyntaxFactory.AccessorDeclaration accessorType
            let accessor = accessor.WithSemicolonToken (SyntaxFactory.Token SyntaxKind.SemicolonToken)

            match visibility with
            | None -> accessor
            | Some visibility ->
                let accessor = accessor.WithLeadingTrivia SyntaxFactory.Space
                accessor.WithModifiers <| VisibilityModifier visibility

    /// Creates a declaration of an auto-implemented property.
    let AutoProperty propertyName propertyType visibility getterVisibility setterVisibility =
        nullOrWhitespaceArg propertyName "propertyName"
        nullOrWhitespaceArg propertyType "propertyType"
        invalidCall (getterVisibility <> None && setterVisibility <> None) "Cannot specify visibility modifiers for both accessors."

        let propertyType = SyntaxFactory.ParseTypeName(propertyType) |> WithLeadingAndTrailingSpace
        let property = SyntaxFactory.PropertyDeclaration (propertyType, (propertyName : string))
        let property = property.WithModifiers <| VisibilityModifier visibility

        let getter = Accessor SyntaxKind.GetAccessorDeclaration getterVisibility |> WithLeadingSpace
        let setter = Accessor SyntaxKind.SetAccessorDeclaration setterVisibility |> WithLeadingAndTrailingSpace

        let accessors = SyntaxFactory.AccessorList (SyntaxFactory.List (getter :: [setter])) |> WithLeadingSpace
        property.WithAccessorList accessors

    /// Creates a lambda function with the given body and arguments.
    let Lambda (arguments : ParameterSyntax list) body =
        nullArg body "body"

        // We construct the lambda with some simple body originally and replace it later on with the real body, as we don't want 
        // to normalize the whitespace of the lambda's body.
        let tempBody = SyntaxFactory.ParseExpression "1"
        match arguments with
        | argument :: [] when argument.Type = null ->
            let lambda = SyntaxFactory.SimpleLambdaExpression (argument, tempBody) |> NormalizeWhitespace
            lambda.WithBody body :> ExpressionSyntax
        | _ ->
            let parameterList = SyntaxFactory.ParameterList (SyntaxFactory.SeparatedList arguments) 
            let lambda = SyntaxFactory.ParenthesizedLambdaExpression (parameterList, tempBody) |> NormalizeWhitespace
            lambda.WithBody body :> ExpressionSyntax