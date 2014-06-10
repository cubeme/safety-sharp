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

namespace SafetySharp.Tests

open SafetySharp.Metamodel
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

exception CompilationException of string

/// Represents a compiled C# compilation unit with a single syntax tree.
type TestCompilation (csharpCode : string) =
    let compilationUnit = SyntaxFactory.ParseCompilationUnit("using SafetySharp.Modeling; " + csharpCode)
    let syntaxTree = compilationUnit.SyntaxTree

    let csharpCompilation = 
        CSharpCompilation
            .Create("TestCompilation")
            .AddReferences(new MetadataFileReference(typeof<obj>.Assembly.Location))
            .AddReferences(new MetadataFileReference(typeof<ComponentSymbol>.Assembly.Location))
            .AddSyntaxTrees(syntaxTree)
            .WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))

    let diagnostics = csharpCompilation.GetDiagnostics() |> Seq.filter (fun diagnostic -> diagnostic.Severity = DiagnosticSeverity.Error)
    do diagnostics |> Seq.iter (fun d -> printfn "%A" d)

    do if not <| Seq.isEmpty diagnostics then
        CompilationException "Failed to create compilation." |> raise

    /// Gets the syntax tree of the compilation.
    member this.SyntaxTree with get () = syntaxTree

    /// Gets the <see cref="CSharpCompilation" /> corresponding to the current instance.
    member this.CSharpCompilation with get () = csharpCompilation

    /// Gets the root syntax node of the syntax tree.
    member this.SyntaxRoot with get () = syntaxTree.GetRoot ()

    /// Gets the semantic model for the compilation's syntax tree.
    member this.SemanticModel with get () = csharpCompilation.GetSemanticModel syntaxTree