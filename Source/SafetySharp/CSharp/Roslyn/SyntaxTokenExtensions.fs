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

open System.Linq
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities

/// Provides extension methods for working with <see cref="SyntaxToken" /> instances.
[<AutoOpen>]
module SyntaxTokenExtensions =
    type SyntaxToken with

        /// Removes all leading and trailing trivia from the syntax token.
        member this.RemoveTrivia () =
            this.WithLeadingTrivia().WithTrailingTrivia ()

        /// Adds the given leading and trailing trivia to the syntax token.
        member this.AddTrivia (leadingTrivia : SyntaxTriviaList) (trailingTrivia : SyntaxTriviaList) =
            this.WithLeadingTrivia(leadingTrivia).WithTrailingTrivia trailingTrivia

        /// Adds the trivia from the given syntax node to the current syntax token.
        member this.AddTriviaFrom (node : SyntaxNode) =
            nullArg node "node"
            this.WithLeadingTrivia(node.GetLeadingTrivia()).WithTrailingTrivia(node.GetTrailingTrivia())

        /// Adds the trivia from the given syntax token to the current syntax token.
        member this.AddTriviaFrom (token : SyntaxToken) =
            this.WithLeadingTrivia(token.LeadingTrivia).WithTrailingTrivia token.TrailingTrivia

        /// Surrounds the syntax token with a single leading and trailing space.
        member this.SurroundWithSingleSpace () =
            this.WithLeadingTrivia(SyntaxFactory.Space).WithTrailingTrivia SyntaxFactory.Space