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

namespace SafetySharp.CSharp.Extensions

open System.Linq
open System.Runtime.CompilerServices
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities

/// Provides extension methods for working with <see cref="SyntaxNode" /> instances.
[<AutoOpen>]
module SyntaxNodeExtensions =
    type SyntaxNode with

        /// Gets a list of descendant syntax nodes of the given type in prefix document order.
        member this.Descendants<'T when 'T :> SyntaxNode> () =
            Requires.NotNull this "this"
            this.DescendantNodes().OfType<'T>()

        /// Gets a list of descendant syntax nodes (including the root node) of the given type 
        /// in prefix document order.
        member this.DescendantsAndSelf<'T when 'T :> SyntaxNode> () =
            Requires.NotNull this "this"
            this.DescendantNodesAndSelf().OfType<'T>()

    [<Extension>]
    type SyntaxNodeExtensions =

        /// Removes all leading and trailing trivia from the syntax node.
        [<Extension>]
        static member inline RemoveTrivia (syntaxNode : 'T when 'T :> SyntaxNode) =
            Requires.NotNull syntaxNode "syntaxNode"
            syntaxNode.WithLeadingTrivia().WithTrailingTrivia()

        /// Adds the given leading and trailing trivia to the syntax node.
        [<Extension>]
        static member inline AddTrivia (syntaxNode : 'T when 'T :> SyntaxNode, leadingTrivia : SyntaxTriviaList, trailingTrivia : SyntaxTriviaList) =
            Requires.NotNull syntaxNode "syntaxNode"
            syntaxNode.WithLeadingTrivia(leadingTrivia).WithTrailingTrivia(trailingTrivia)

        /// Adds the trivia from the given syntax node to the current syntax node.
        [<Extension>]
        static member inline AddTriviaFrom (syntaxNode : 'T when 'T :> SyntaxNode, node : SyntaxNode) =
            Requires.NotNull syntaxNode "syntaxNode"
            syntaxNode.WithLeadingTrivia(node.GetLeadingTrivia()).WithTrailingTrivia(node.GetTrailingTrivia())

        /// Surrounds the syntax node with a single leading and trailing space.
        [<Extension>]
        static member inline SurroundWithSingleSpace (syntaxNode : 'T when 'T :> SyntaxNode) =
            Requires.NotNull syntaxNode "syntaxNode"
            syntaxNode.WithLeadingTrivia(SyntaxFactory.Space).WithTrailingTrivia(SyntaxFactory.Space)