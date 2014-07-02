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

/// Provides extension methods for working with <see cref="IPropertySymbol" /> instances.
[<AutoOpen>]
module internal PropertySymbolExtensions =
    type IPropertySymbol with

        /// Checks whether the property symbol overrides the given property.
        member this.Overrides (overriddenProperty : IPropertySymbol) =
            nullArg this "this"
            nullArg overriddenProperty "overriddenProperty"

            if this.Equals overriddenProperty then
                true
            elif not this.IsOverride then
                false
            elif this.OverriddenProperty.Equals overriddenProperty then
                true
            else
                this.OverriddenProperty.Overrides overriddenProperty

        /// Checks whether the property is marked with the given attribute.
        member this.HasAttribute (attributeType : INamedTypeSymbol) =
            nullArg this "this"
            this.GetAttributes () |> Seq.exists (fun attribute -> attribute.AttributeClass = attributeType)

        /// Checks whether the property is marked with the given attribute.
        member this.HasAttribute<'T when 'T :> Attribute> (compilation : Compilation) =
            nullArg compilation "compilation"
            this.HasAttribute (compilation.GetTypeSymbol<'T> ())