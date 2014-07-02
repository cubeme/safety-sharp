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

namespace SafetySharp.Internal.CSharp

open System
open System.Reflection
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open SafetySharp.Internal.Utilities
open SafetySharp.Modeling.CompilerServices

/// Represents a Safety Sharp modeling assembly.
type internal ModelingAssembly (modelingAssembly : Assembly) as this=

    do nullArg modelingAssembly "modelingAssembly"

    let assemblyMetadata = modelingAssembly.GetCustomAttribute<ModelingAssemblyAttribute> ()
    do invalidArg (obj.ReferenceEquals(assemblyMetadata, null)) "modelingAssembly" "Expected a SafetySharp modeling assembly."

    do if this.CompilerVersion <> Compiler.Version then
        invalidOp "Modeling assembly '%s' was compiled with a different version of the SafetySharp compiler." modelingAssembly.FullName 

    /// Gets the version string of the Safety Sharp compiler that was used to compile the modeling assembly.
    member this.CompilerVersion = assemblyMetadata.CompilerVersion

    /// Gets the modeling assemblies this modeling assembly depends on.
    member this.DependentAssemblies =
        modelingAssembly.GetReferencedAssemblies ()
        |> Seq.map Assembly.Load
        |> Seq.where ModelingAssembly.IsModelingAssembly
        |> Seq.map (fun assembly -> ModelingAssembly assembly)

    /// Gets the C# <see cref="SyntaxTree" />s of all compilation units of the modeling assembly.
    member this.CompilationUnits =
        modelingAssembly.GetCustomAttributes<ModelingCompilationUnitAttribute> ()
        |> Seq.map (fun compilationUnit -> compilationUnit.SyntaxTree)

    /// Returns a <see cref="ModelingAssembly" /> instance wrapping the given assembly if the assembly is a modeling assembly.
    static member private IsModelingAssembly (assembly : Assembly) =
        assembly.GetCustomAttribute<ModelingAssemblyAttribute> () <> null

    /// Gets the C# <see cref="Compilation" /> representing the source code of the modeling assembly and of all of its dependent
    /// modeling assemblies.
    member this.Compilation =
        let options = CSharpCompilationOptions OutputKind.DynamicallyLinkedLibrary
        let compilation = CSharpCompilation.Create(modelingAssembly.GetName().Name).WithOptions(options)
        let compilation = compilation.AddReferences (MetadataFileReference typeof<obj>.Assembly.Location)
        let compilation = compilation.AddReferences (MetadataFileReference typeof<ModelingAssembly>.Assembly.Location)
        let compilation = compilation.AddReferences (MetadataFileReference typeof<System.Linq.Expressions.Expression>.Assembly.Location)
        this.AddCompilationUnits compilation

    /// Adds the modeling assembly's compilation units and all compilation units of the assembly's dependent modeling assemblies to the
    /// <paramref name="compilation" />.
    member private this.AddCompilationUnits (compilation : CSharpCompilation) =
        let compilation = 
            this.DependentAssemblies
            |> Seq.fold (fun compilation assembly -> assembly.AddCompilationUnits compilation) compilation

        compilation.AddSyntaxTrees this.CompilationUnits