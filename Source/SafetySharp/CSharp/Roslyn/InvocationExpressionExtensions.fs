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

open System
open System.Linq
open System.Text
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Utilities
open SafetySharp.Modeling

/// Provides extension methods for working with <see cref="InvocationExpressionSyntax" /> instances.
[<AutoOpen>]
module internal InvocationExpressionExtensions =
    type InvocationExpressionSyntax with

        /// Checks whether the invocation expression invokes a CTL or LTL formula function.
        member this.IsFormulaFunction (semanticModel : SemanticModel) =
            nullArg this "this"
            nullArg semanticModel "semanticModel"

            let methodSymbol = semanticModel.GetReferencedSymbol<IMethodSymbol> this
            let methodClass = methodSymbol.ContainingType
            methodClass = semanticModel.GetTypeSymbol<Ltl> () ||
                methodClass = semanticModel.GetTypeSymbol<Ctl> () ||
                methodClass = semanticModel.GetTypeSymbol<CtlOperatorFactory> () ||
                methodClass = semanticModel.GetTypeSymbol<LtlFormula> () ||
                methodClass = semanticModel.GetTypeSymbol<CtlFormula> ()