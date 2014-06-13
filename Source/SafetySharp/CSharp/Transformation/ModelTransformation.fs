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

open System.Collections.Immutable
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Utilities

/// Represents a configuration of symbols, objects, and formulas that allows a transformation of the model
/// to a modelchecker in order to verify the formulas.
type Configuration = {
    /// The method symbol of the configuration, containing all symbols used throughout the model.
    ModelSymbol : ModelSymbol

    /// The model object of the configuration, containing all partition and component objects used throughout the model.
    ModelObject : ModelObject

    /// The formulas defined over the symbols and objects that require verification.
    Formulas : Formula list

    /// Resolves the body of a component's method.
    MethodBodyResolver : Map<ComponentSymbol * MethodSymbol, Statement>
}

module ModelTransformation =

    /// Transforms a modeling compilation and a model instance to the metamodel types.
    let Transform (compilation : ModelingCompilation) (model : Model) =
        Requires.NotNull model "model"
        Requires.ArgumentSatisfies model.IsMetadataFinalized "model" "The model metadata has not yet been finalized."

        let symbolResolver = SymbolTransformation.Transform compilation.CSharpCompilation
        let objectResolver = ObjectTransformation.Transform model symbolResolver

        {
            ModelSymbol = symbolResolver.ModelSymbol
            ModelObject = objectResolver.ModelObject
            Formulas = []
            MethodBodyResolver = StatementTransformation.TransformMethodBodies compilation.CSharpCompilation symbolResolver
        }