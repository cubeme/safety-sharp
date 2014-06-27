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

namespace SafetySharp.CSharp.Transformation

open System.Collections.Immutable
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Utilities
open Microsoft.CodeAnalysis

module internal ModelTransformation =

    /// Transforms a modeling compilation and a model instance to the metamodel types.
    let Transform (compilation : Compilation) (model : Model) (formulas : CSharpFormula list) =
        nullArg model "model"
        invalidArg (not model.IsMetadataFinalized) "model" "The model metadata has not yet been finalized."

        let symbolResolver = SymbolTransformation.Transform compilation model
        let objectResolver = ObjectTransformation.Transform model symbolResolver

        {
            ModelSymbol = symbolResolver.ModelSymbol
            ModelObject = objectResolver.ModelObject
            Formulas = formulas |> List.map (FormulaTransformation.Transform symbolResolver objectResolver)
            MethodBodyResolver = StatementTransformation.TransformMethodBodies compilation symbolResolver
        }