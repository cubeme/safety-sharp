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

namespace SafetySharp.Internal.CSharp.Roslyn

open System
open System.Linq
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.Utilities

/// Provides extension methods for working with <see cref="MethodDeclarationSyntax" /> instances.
[<AutoOpen>]
module internal MethodDeclarationExtensions =
    type MethodDeclarationSyntax with

        /// Checks whether the method declaration declares a method overriding the <see cref="Component.Update()" /> method.
        member this.IsUpdateMethod (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"
            semanticModel.DeclaredSymbolOf(this).IsUpdateMethod semanticModel

        /// Gets the visibility of the method.
        member this.Visibility =
            nullArg this "this"
            let defaultVisibility = if this.ExplicitInterfaceSpecifier = null then Private else Public
            this.Modifiers.GetVisibility defaultVisibility

        /// Gets the <see cref="System.Action{}" /> or <see cref="System.Func{}" /> delegate type corresponding to the
        /// method declaration.
        member this.GetDelegateType (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"

            let typeArguments = this.ParameterList.Parameters |> Seq.map (fun parameter -> parameter.Type.ToString ())

            let generateType delegateType (typeArguments : string seq) =
                if typeArguments |> Seq.isEmpty then
                    "System.Action"
                else
                    sprintf "%s<%s>" delegateType (String.Join (", ", typeArguments))

            match semanticModel.GetReferencedSymbol<INamedTypeSymbol>(this.ReturnType).SpecialType with
            | SpecialType.System_Void ->
                generateType "System.Action" typeArguments
            | _ -> 
                let typeArguments = seq { yield! typeArguments; yield this.ReturnType.ToString () }
                generateType "System.Func" typeArguments

        /// Checks whether the method is marked with the given attribute.
        member this.HasAttribute<'T when 'T :> Attribute> (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"
            semanticModel.DeclaredSymbolOf(this).HasAttribute<'T> semanticModel.Compilation