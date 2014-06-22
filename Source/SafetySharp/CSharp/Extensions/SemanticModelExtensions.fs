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

open System
open System.Linq
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities
open SafetySharp.Modeling

/// Provides extension methods for working with <see cref="SemanticModel" /> instances.
[<AutoOpen>]
module SemanticModelExtensions =
    
    /// Gets the <see cref="IMethodSymbol" /> corresponding to the one of the methods of the <see cref="Choose"/> class.
    let private getChooseMethodSymbol (semanticModel : SemanticModel) methodName specialType parameterCount =
        let methods = 
            semanticModel.Compilation.GetTypeByMetadataName(typeof<Choose>.FullName).GetMembers(methodName).OfType<IMethodSymbol>()
            |> Seq.where (fun method' -> 
                method'.Parameters.Length = parameterCount && 
                (method'.Parameters.Length = 0 || method'.Parameters.[0].Type.SpecialType = specialType)
            )
            |> List.ofSeq

        let raiseException prefix =
            invalidOp "%s Choose method with name = '%s', parameter count = %i, parameter type = '%A'." prefix methodName parameterCount specialType 

        match methods with
        | method' :: [] -> method'
        | [] -> raiseException "Unable to find"
        | _ -> raiseException "Found more than one"

    type SemanticModel with
       
        /// Gets the <see cref="IMethodSymbol" /> representing the <see cref="Component.Literal{T}()" />
        /// method within the context of the <paramref name="semanticModel" />.
        member this.GetChooseLiteralMethodSymbol normalizedVersion =
            nullArg this "this"
            getChooseMethodSymbol this "Literal" SpecialType.None (if normalizedVersion then 1 else 0)

        /// Gets the <see cref="IMethodSymbol" /> representing the <see cref="Choose.Boolean()" />
        /// method within the context of the <paramref name="semanticModel" />.
        member this.GetChooseBooleanMethodSymbol normalizedVersion =
            nullArg this "this"
            getChooseMethodSymbol this "Boolean" SpecialType.System_Boolean (if normalizedVersion then 1 else 0)

        /// Gets the <see cref="IMethodSymbol" /> representing one of the 'Choose.Value()' methods within the
        /// context of the <paramref name="semanticModel" />.
        member this.GetChooseValueMethodSymbol normalizedVersion specialType =
            nullArg this "this"
            getChooseMethodSymbol this "Value" specialType (if normalizedVersion then 2 else 3)

        /// Gets the <see cref="IMethodSymbol " /> representing one of the 'Choose.FromRange()' methods within
        /// the context of the <paramref name="semanticModel" />.
        member this.GetChooseFromRangeMethodSymbol normalizedVersion specialType =
            nullArg this "this"
            getChooseMethodSymbol this "FromRange" specialType (if normalizedVersion then 3 else 2)

        /// Gets the <see cref="ITypeSymbol" /> representing the given type within the context of
        /// the semantic model.
        member this.GetTypeSymbol<'T> () =
            nullArg this "this"
            this.Compilation.GetTypeSymbol<'T> ()

        /// Gets the <see cref="ITypeSymbol" /> representing the given type within the context of
        /// the semantic model.
        member this.GetTypeSymbol (typeInfo : Type) =
            nullArg this "this"
            nullArg typeInfo "typeInfo"
            this.Compilation.GetTypeSymbol typeInfo

        /// Gets the <see cref="ITypeSymbol" /> representing the given type within the context of
        /// the semantic model.
        member this.GetTypeSymbol name =
            nullArg this "this"
            nullOrWhitespaceArg name "name"
            this.Compilation.GetTypeSymbol name

        /// Gets the <see cref="ITypeSymbol " /> representing the <see cref="Component" /> class within the
        /// context of the semantic model.
        member this.GetComponentClassSymbol () =
            nullArg this "this"
            this.Compilation.GetComponentClassSymbol ()

        /// Gets the <see cref="ITypeSymbol " /> representing the <see cref="IComponent" /> interface within the
        /// context of the semantic model.
        member this.GetComponentInterfaceSymbol () =
            nullArg this "this"
            this.Compilation.GetComponentInterfaceSymbol ()

        /// Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Update()" /> method
        /// within the context of the semantic model.
        member this.GetUpdateMethodSymbol () =
            nullArg this "this"
            this.Compilation.GetUpdateMethodSymbol ()

        /// Gets the symbol corresponding to the given syntax node.
        member this.GetSymbol<'T when 'T :> ISymbol> (node : SyntaxNode) =
            nullArg this "this"
            nullArg node "node"

            match this.GetSymbolInfo(node).Symbol with
            | :? 'T as symbol -> symbol
            | null -> invalidOp "Unable to determine symbol for syntax node '%A'." node
            | symbol -> 
                invalidOp "Expected a symbol of type '%s'. However, the actual symbol type for syntax node '%A' is '%s'."
                          typeof<'T>.FullName node (symbol.GetType().FullName)