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

namespace SafetySharp.Tests.CSharp

open System
open System.Collections.Generic
open System.Linq
open System.IO
open System.Reflection
open SafetySharp.Metamodel
open SafetySharp.CSharp
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

type CompilationException (message : string) =
    inherit Exception (message)

[<AutoOpen>]
module private Exception =
    let inline failed message = new CompilationException(message) |> raise

/// Represents a compiled C# compilation unit with a single syntax tree.
type internal TestCompilation (csharpCode : string) =
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

    /// Emits an in-memory assembly for the compilation and loads the assembly into the app domain.
    member this.Compile () =
        use stream = new MemoryStream ()
        let emitResult = csharpCompilation.Emit stream

        if (emitResult.Success) then
            stream.ToArray () |> Assembly.Load
        else
            for diagnostic in emitResult.Diagnostics do
                printf "%A" diagnostic

            failed "Assembly compilation failed."

    /// <summary>
    /// Finds the <see cref="TypeDeclarationSyntax" /> for the type with the given name in the compilation.
    /// Throws an exception if more than one type with the given name was found.
    /// </summary>
    member this.FindTypeDeclaration typeName =
        let types = 
            this.SyntaxRoot
                .DescendantsAndSelf<TypeDeclarationSyntax>()
                .Where(fun typeDeclaration -> 
                    let symbol = this.SemanticModel.GetDeclaredSymbol typeDeclaration
                    symbol.ToDisplayString SymbolDisplayFormat.MinimallyQualifiedFormat = typeName
                )
                .ToArray();

        if types.Length = 0 then
            sprintf "Found no type with name '%s'." typeName |> failed

        if types.Length > 1 then
            sprintf "Found more than one type with name '%s'." typeName |> failed

        types.[0]

    /// <summary>
    /// Finds the <see cref="ClassDeclarationSyntax" /> for the class with the given name in the compilation.
    /// Throws an exception if more than one class with the given name was found.
    /// </summary>
    member this.FindClassDeclaration className =
        match this.FindTypeDeclaration(className) with
        | :? ClassDeclarationSyntax as classDeclaration -> classDeclaration
        | _ -> sprintf "Found no class with name '%s'." className |> failed

    /// <summary>
    /// Finds the <see cref="InterfaceDeclarationSyntax" /> for the interface with the given name in the
    /// compilation. Throws an exception if more than one interface with the given name was found.
    /// </summary>
    member this.FindInterfaceDeclaration interfaceName =
        match this.FindTypeDeclaration(interfaceName) with
        | :? InterfaceDeclarationSyntax as interfaceDeclaration -> interfaceDeclaration
        | _ -> sprintf "Found no interface with name '%s'." interfaceName |> failed

    /// <summary>
    /// Finds the <see cref="MethodDeclarationSyntax" /> for the method with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or method with the given name was found.
    /// </summary>
    member this.FindMethodDeclaration typeName methodName =
        let methods = 
            this.FindTypeDeclaration(typeName)
                .DescendantsAndSelf<MethodDeclarationSyntax>()
                .Where(fun methodDeclaration -> methodDeclaration.Identifier.ValueText = methodName)
                .ToArray();

        if methods.Length = 0 then
            sprintf "Found no methods with name '%s' in '%s'." methodName typeName |> failed

        if methods.Length > 1 then
            sprintf "Found more than one method with name '%s' in '%s'." methodName typeName |> failed

        methods.[0]

    /// <summary>
    /// Finds the <see cref="VariableDeclaratorSyntax" /> for the field with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or field with the given name was found.
    /// </summary>
    member this.FindFieldDeclaration typeName fieldName =
        let fields = 
            this.FindTypeDeclaration(typeName)
                .DescendantsAndSelf<FieldDeclarationSyntax>()
                .SelectMany(fun fieldDeclaration -> fieldDeclaration.Declaration.Variables :> IEnumerable<VariableDeclaratorSyntax>)
                .Where(fun variableDeclaration -> variableDeclaration.Identifier.ValueText = fieldName)
                .ToArray();

        if fields.Length = 0 then
            sprintf "Found no fields with name '%s' in '%s'." fieldName typeName |> failed

        if fields.Length > 1 then
            sprintf "Found more than one field with name '%s' in '%s'." fieldName typeName |> failed

        fields.[0]

    /// <summary>
    /// Gets the <see cref="ITypeSymbol" /> representing the type with the given name.
    /// </summary>
    member this.FindTypeSymbol typeName =
        this.FindTypeDeclaration typeName |> this.SemanticModel.GetDeclaredSymbol

    /// <summary>
    /// Gets the <see cref="ITypeSymbol" /> representing the class with given name.
    /// </summary>
    member this.FindClassSymbol className =
        this.FindClassDeclaration className |> this.SemanticModel.GetDeclaredSymbol

    /// <summary>
    /// Gets the <see cref="ITypeSymbol" /> representing the interface with the given name.
    /// </summary>
    member this.FindInterfaceSymbol interfaceName =
        this.FindInterfaceDeclaration interfaceName |> this.SemanticModel.GetDeclaredSymbol

    /// <summary>
    /// Gets the <see cref="IMethodSymbol" /> representing the method with the given name in the type with
    /// with the given name.
    /// </summary>
    member this.FindMethodSymbol className methodName =
        this.FindMethodDeclaration className methodName |> this.SemanticModel.GetDeclaredSymbol

    /// <summary>
    /// Gets the <see cref="IFieldSymbol" /> representing the field with the given name in the type with
    /// the given name.
    /// </summary>
    member this.FindFieldSymbol className fieldName =
        this.FindFieldDeclaration className fieldName |> this.SemanticModel.GetDeclaredSymbol :?> IFieldSymbol