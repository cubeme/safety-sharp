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

module internal SafetySharp.Compiler.CSharp

open System
open System.IO

open ICSharpCode.NRefactory
open ICSharpCode.NRefactory.CSharp
open ICSharpCode.NRefactory.CSharp.Resolver
open ICSharpCode.NRefactory.Semantics
open ICSharpCode.NRefactory.TypeSystem

open SafetySharp.Compiler.Model
open SafetySharp.Compiler.NRefactory

// ======================================================================================================================================
// NRefactory Conversion Functions
// ======================================================================================================================================

/// Creates a SourceInfo instance for the given NRefactory AstNode.
let toSourceInfo context (node : AstNode) = {  
    File = context.SyntaxTree.FileName
    BeginLine = node.StartLocation.Line
    BeginColumn = node.StartLocation.Column
    EndLine = node.EndLocation.Line
    EndColumn = node.EndLocation.Column
}

/// Creates an Identifier for the given NRefactory Identifier
let toIdentifier context (identifier : ICSharpCode.NRefactory.CSharp.Identifier) = { 
    Identifier.Name = identifier.Name
    Identifier.SourceInfo = toSourceInfo context identifier
}

/// Creates an EnumDeclaration for the given NRefactory TypeDeclaration.
let toEnumDeclaration context (enum : TypeDeclaration) = { 
    SourceInfo = toSourceInfo context enum
    Name = toIdentifier context enum.NameToken
    Namespace = resolveNamespace context enum
    Members = 
        getDescendants<EnumMemberDeclaration> enum
        |> Seq.map (fun m -> toIdentifier context m.NameToken)
        |> Seq.toList
}

let resolveTypes context =
    let enumeration = 
        getDescendantsAndSelf<TypeDeclaration> context.SyntaxTree
        |> Seq.filter (fun t -> t.ClassType = ClassType.Enum)
        |> Seq.head

    let enum = toEnumDeclaration context enumeration
    enum

let CompileProject projectFile =
    let project = CSharpProjectContent ()
    let loader = CecilLoader();

    let assembly = [| loader.LoadAssemblyFile (typeof<int>.Assembly.Location) :> IAssemblyReference |]
    let project = project.AddAssemblyReferences assembly

    let parser = CSharpParser ()
    let path = Path.Combine (Path.GetDirectoryName projectFile, "LightBarrier.cs")
    let syntaxTree = parser.Parse (File.ReadAllText path, path)
    let unresolvedFile = syntaxTree.ToTypeSystem ()

    let project = project.AddOrUpdateFiles unresolvedFile

    let compilation = project.CreateCompilation ()
    let resolver = CSharpAstResolver (compilation, syntaxTree, unresolvedFile)

    resolveTypes { SyntaxTree = syntaxTree; Resolver = resolver }