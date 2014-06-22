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
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities

/// Provides extension methods for working with <see cref="TypeDeclarationSyntax" /> instances.
[<AutoOpen>]
module TypeDeclarationExtensions =
    type TypeDeclarationSyntax with

        /// Checks whether the type declaration declaration is a component declaration.
        member this.IsComponentDeclaration (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"
            this.IsDerivedFrom semanticModel <| semanticModel.GetComponentClassSymbol ()

        /// Checks whether type declaration is a component interface declaration.
        member this.IsComponentInterfaceDeclaration (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"
            this.IsDerivedFrom semanticModel <| semanticModel.GetComponentInterfaceSymbol ()

        /// Checks whether the type declaration is directly or indirectly derived from the <paramref name="baseType" /> interface or class.
        member this.IsDerivedFrom (semanticModel : SemanticModel) (baseType : ITypeSymbol) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"
            nullArg baseType "baseType"
            semanticModel.GetSymbol(this).IsDerivedFrom baseType
