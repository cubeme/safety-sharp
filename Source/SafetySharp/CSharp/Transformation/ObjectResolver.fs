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
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Utilities

/// Represents a mapping between the original .NET objects and the created metamodel symbols and objects.
type internal ObjectResolver = private {
    ComponentSymbolMap : ImmutableDictionary<Component, ComponentSymbol>
    ComponentObjectMap : ImmutableDictionary<Component, ComponentObject>
    Model : ModelObject
}
    with

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given .NET component object.
    member this.ResolveSymbol (componentObject : Component) =
        Requires.NotNull componentObject "componentObject"
        match this.ComponentSymbolMap.TryGetValue componentObject with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "componentObject" "The given component is unknown."

    /// Resolves the <see cref="ComponentObject"/> corresponding to the given .NET component object.
    member this.ResolveObject (componentObject : Component) =
        Requires.NotNull componentObject "componentObject"
        match this.ComponentObjectMap.TryGetValue componentObject with
        | (result, symbol) when result -> symbol
        | _ -> invalidArg "componentObject" "The given component is unknown."

    /// Gets the model object that contains all of the resolver's component and partition objects.
    member this.ModelObject = this.Model