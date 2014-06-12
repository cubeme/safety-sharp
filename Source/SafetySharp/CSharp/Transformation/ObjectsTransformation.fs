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

/// Represents a mapping between the original .NET objects and the created metamodel symbols and objects.
type ObjectResolver = private {
    ComponentSymbolMap : ImmutableDictionary<Component, ComponentSymbol>
    ComponentObjectMap : ImmutableDictionary<Component, ComponentObject>
}
    with

    /// Resolves the <see cref="ComponentSymbol"/> corresponding to the given .NET component object.
    member this.ResolveSymbol (dotNetComponent : Component) =
        Requires.NotNull dotNetComponent "dotNetComponent'"
        Requires.That (this.ComponentSymbolMap.ContainsKey dotNetComponent) "The given component is unknown."
        this.ComponentSymbolMap.[dotNetComponent]

    /// Resolves the <see cref="ComponentObject"/> corresponding to the given .NET component object.
    member this.ResolveObject (dotNetComponent : Component) =
        Requires.NotNull dotNetComponent "dotNetComponent'"
        Requires.That (this.ComponentObjectMap.ContainsKey dotNetComponent) "The given component is unknown."
        this.ComponentObjectMap.[dotNetComponent]

module ObjectsTransformation =

    /// Transforms C# objects to metamodel objects.
    let Transform (model : Model) =
        Requires.NotNull model "model"
        Requires.ArgumentSatisfies model.IsMetadataFinalized "model" "The model metadata has not yet been finalized."