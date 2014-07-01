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

namespace SafetySharp.Internal.CSharp.Normalization

open System
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open SafetySharp.Internal.CSharp.Roslyn

/// Indicates which parts of the code are affected by a normalizer.
[<RequireQualifiedAccess>]
type internal NormalizationScope =
    /// Limits the scope of the normalizer to all members of a component class.
    | Components
    /// Limits the scope of the normalizer to all statements (excluding those of the constructors) of a component class.
    | ComponentStatements
    /// Does not limit the scope of the normalizer.
    | Global

/// A base class for C# normalizers that normalize certain C# features to equivalent ones that are easier to transform to
/// the metamodel.
[<AbstractClass>]
type internal CSharpNormalizer (scope) =
    inherit CSharpSyntaxRewriter ()

    /// The semantic model that should be used for semantic analysis during normalization.
    [<DefaultValue>] val mutable semanticModel : SemanticModel

    /// Normalizes the given syntax tree of the compilation.
    member private this.NormalizeSyntaxTree (compilation : Compilation) (syntaxTree : SyntaxTree) =
        this.semanticModel <- compilation.GetSemanticModel syntaxTree

        let root = syntaxTree.GetRoot ()
        let normalizedRoot = this.Visit root

        if root = normalizedRoot then
            syntaxTree
        else
            syntaxTree.WithChangedText (normalizedRoot.GetText ())

    /// Normalizes the C# code contained in <paramref name="compilation." />
    member this.Normalize (compilation : Compilation) =
        compilation.SyntaxTrees 
        |> Seq.fold (fun (compilation : Compilation) syntaxTree -> 
            compilation.ReplaceSyntaxTree (syntaxTree, this.NormalizeSyntaxTree compilation syntaxTree)
        ) compilation

    /// Ensures that non-component classes are only visited when the normalizer as global scope.
    override this.VisitClassDeclaration node =
        if scope = NormalizationScope.Global || node.IsComponentDeclaration this.semanticModel then
            base.VisitClassDeclaration node
        else
            upcast node

    /// Ensures that a constructor is only visited when the normalizer as global scope.
    override this.VisitConstructorDeclaration node =
        if scope <> NormalizationScope.ComponentStatements then
            base.VisitConstructorDeclaration node
        else
            upcast node