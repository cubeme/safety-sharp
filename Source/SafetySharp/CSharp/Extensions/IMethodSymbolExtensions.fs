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

namespace SafetySharp.CSharp

open System.Linq
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities

/// Provides extension methods for working with <see cref="IMethodSymbol" /> instances.
[<AutoOpen>]
module internal MethodSymbolExtensions =
    type IMethodSymbol with

        /// Checks whether the method symbol overrides the given method.
        member this.Overrides (overriddenMethod : IMethodSymbol) =
            Requires.NotNull this "this"
            Requires.NotNull overriddenMethod "overriddenMethod"

            if not this.IsOverride then
                false
            else if this.OverriddenMethod.Equals overriddenMethod then
                true
            else
                this.OverriddenMethod.Overrides overriddenMethod

        /// Checks whether the method symbol overrides the <see cref="Component.Update()" /> method.
        member this.IsUpdateMethod (semanticModel : SemanticModel) =
            Requires.NotNull this "this"
            this.Overrides <| semanticModel.GetUpdateMethodSymbol ()