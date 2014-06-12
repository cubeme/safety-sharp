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
open SafetySharp.Modeling

/// Provides extension methods for working with <see cref="Compilation" /> instances.
[<AutoOpen>]
module CompilationExtensions =
    type Compilation with

        /// Gets the <see cref="ITypeSymbol" /> representing the given type within the context of the compilation.
        member this.GetTypeSymbol<'T> () =
            Requires.NotNull this "this"
            this.GetTypeSymbol typeof<'T>.FullName;

        /// Gets the <see cref="ITypeSymbol" /> representing the given type within the context of the compilation.
        member this.GetTypeSymbol name =
            Requires.NotNull this "this"
            Requires.NotNullOrWhitespace name "name"

            this.GetTypeByMetadataName name;

        /// Gets the <see cref="ITypeSymbol " /> representing the <see cref="Component" /> class within the
        /// context of the compilation.
        member this.GetComponentClassSymbol () =
            Requires.NotNull this "this"
            this.GetTypeByMetadataName(typeof<Component>.FullName);

        /// Gets the <see cref="ITypeSymbol " /> representing the <see cref="IComponent" /> interface within the
        /// context of the compilation.
        member this.GetComponentInterfaceSymbol () =
            Requires.NotNull this "this"
            this.GetTypeByMetadataName(typeof<IComponent>.FullName);

        /// Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Update()" /> method
        /// within the context of the compilation.
        member this.GetUpdateMethodSymbol () =
            Requires.NotNull this "this"
            this.GetComponentClassSymbol().GetMembers("Update").OfType<IMethodSymbol>().Single()

        /// Gets the symbols for all types contained in the compilation except for types defined in mscorlib or in SafetySharp.dll.
        member this.GetTypeSymbols () =
            let mscorlib = this.ObjectType.ContainingAssembly
            let safetySharp = this.GetComponentClassSymbol().ContainingAssembly

            let rec enumerateSymbols (symbol : ISymbol) = seq {
                if symbol.ContainingAssembly = mscorlib || symbol.ContainingAssembly = safetySharp then
                    ()
                else
                    match symbol with
                    | :? ITypeSymbol as typeSymbol -> 
                        yield typeSymbol
                        yield! typeSymbol.GetMembers () |> Seq.collect enumerateSymbols
                    | :? INamespaceSymbol as namespaceSymbol -> 
                        yield! namespaceSymbol.GetMembers () |> Seq.collect enumerateSymbols
                    | _ -> ()
            }

            enumerateSymbols this.GlobalNamespace