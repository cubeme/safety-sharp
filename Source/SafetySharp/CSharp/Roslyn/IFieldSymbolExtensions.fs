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

open System.Linq
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.Utilities

/// Provides extension methods for working with <see cref="IFieldSymbol" /> instances.
[<AutoOpen>]
module internal FieldSymbolExtensions =

    /// Checks whether the type of the given field implements the component interface.
    /// Note that it is sufficient to check whether the type implements IComponent, as all 
    /// Component derived classes implement IComponent as well.
    let private isSubcomponentField (fieldInfo : IFieldSymbol) (componentInterfaceSymbol : ITypeSymbol) =
        fieldInfo.Type.IsDerivedFrom(componentInterfaceSymbol) || fieldInfo.Type.Equals(componentInterfaceSymbol);

    type IFieldSymbol with

        /// Checks whether the field symbol is a subcomponent field.
        member this.IsSubcomponentField (compilation : Compilation) =
            nullArg this "this"
            nullArg compilation "compilation"
            compilation.GetComponentInterfaceSymbol () |> isSubcomponentField this

        /// Checks whether the field symbol is a subcomponent field.
        member this.IsSubcomponentField (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"
            semanticModel.Compilation.GetComponentInterfaceSymbol () |> isSubcomponentField this
