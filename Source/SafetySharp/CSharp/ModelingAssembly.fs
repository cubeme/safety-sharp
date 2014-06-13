﻿// The MIT License (MIT)
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

open System
open System.Reflection
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open SafetySharp.Utilities
open SafetySharp.Modeling

/// Represents a Safety Sharp modeling assembly.
type ModelingAssembly (modelingAssembly : Assembly) as this=

    do Requires.NotNull modelingAssembly "modelingAssembly"

    let assemblyMetadata = modelingAssembly.GetCustomAttribute<ModelingAssemblyAttribute> ()
    do Requires.ArgumentSatisfies (not <| obj.ReferenceEquals(assemblyMetadata, null)) "modelingAssembly" "Expected a SafetySharp modeling assembly."

    do if this.CompilerVersion <> Compiler.Version then
        sprintf "Modeling assembly '%s' was compiled with a different version of the SafetySharp compiler." modelingAssembly.FullName 
        |> invalidOp

    /// Gets the version string of the Safety Sharp compiler that was used to compile the modeling assembly.
    member this.CompilerVersion = assemblyMetadata.CompilerVersion

    /// Gets the C# <see cref="Compilation" /> representing the source code of the modeling assembly and of all of its dependent
    /// modeling assemblies.
    member this.Compilation =
        let options = CSharpCompilationOptions OutputKind.DynamicallyLinkedLibrary
        let compilation = CSharpCompilation.Create("ModelingAssemblyMetadata").WithOptions(options)

        let compilation = 
            modelingAssembly.GetReferencedAssemblies()
            |> Seq.map Assembly.Load
            |> Seq.fold (fun (compilation : CSharpCompilation) assembly -> compilation.AddReferences (MetadataFileReference assembly.Location)) compilation

        ModelingCompilation (this.AddCompilationUnits compilation)

    /// Gets the modeling assemblies this modeling assembly depends on.
    member this.DependentAssemblies =
        modelingAssembly.GetCustomAttributes<ModelingAssemblyReferenceAttribute> ()
        |> Seq.map (fun assembly -> ModelingAssembly (Assembly.Load assembly.AssemblyName))

    /// Gets the C# <see cref="SyntaxTree" />s of all compilation units of the modeling assembly.
    member this.CompilationUnits =
        modelingAssembly.GetCustomAttributes<ModelingCompilationUnitAttribute> ()
        |> Seq.map (fun compilationUnit -> compilationUnit.SyntaxTree)

    /// Adds the modeling assembly's compilation units and all compilation units of the assembly's dependent assemblies to the
    /// <paramref name="compilation" />.
    member private this.AddCompilationUnits (compilation : CSharpCompilation) =
        let compilation = 
            this.DependentAssemblies
            |> Seq.fold (fun compilation assembly -> assembly.AddCompilationUnits compilation) compilation

        compilation.AddSyntaxTrees this.CompilationUnits
