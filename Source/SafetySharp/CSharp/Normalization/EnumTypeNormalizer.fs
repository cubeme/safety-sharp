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
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp.Roslyn
open SafetySharp.Modeling

/// Replaces all uses of enum types within a component by int.
type internal EnumTypeNormalizer () =
    inherit CSharpNormalizer (NormalizationScope.Components)

    let intType = SyntaxFactory.ParseTypeName "int"

    member private this.ReplaceEnumType (nameSyntax : NameSyntax) =
        match this.semanticModel.GetSymbolInfo(nameSyntax).Symbol with
        | :? ITypeSymbol as typeSymbol when typeSymbol.TypeKind = TypeKind.Enum ->
            intType |> Syntax.WithTriviaFromNode nameSyntax :> SyntaxNode
        | _ ->
            nameSyntax :> SyntaxNode

    override this.VisitAliasQualifiedName node = this.ReplaceEnumType node
    override this.VisitQualifiedName node = this.ReplaceEnumType node
    override this.VisitIdentifierName node = this.ReplaceEnumType node

    override this.VisitMemberAccessExpression node = 
        // We want to rewrite enum literals such as 'E.A' to 'int.A'...
        upcast node