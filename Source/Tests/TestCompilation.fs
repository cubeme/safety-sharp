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

open System
open System.Collections.Generic
open System.Linq
open System.IO
open System.Reflection
open System.Threading
open SafetySharp.Metamodel
open SafetySharp.CSharp
open SafetySharp.CSharp.Extensions
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics

type CompilationException (message : string) =
    inherit Exception (message)

/// Represents a compiled C# compilation unit with a single syntax tree.
type internal TestCompilation (csharpCode : string) =
    let mutable (assembly : Assembly) = null
    let failed message = CompilationException message |> raise

    let compilationUnit = SyntaxFactory.ParseCompilationUnit("using SafetySharp.Modeling; " + csharpCode)
    let syntaxTree = compilationUnit.SyntaxTree

    let csharpCompilation = 
        CSharpCompilation
            .Create(TestCompilation.CompilationName)
            .AddReferences(MetadataFileReference typeof<obj>.Assembly.Location)
            .AddReferences(MetadataFileReference typeof<ComponentSymbol>.Assembly.Location)
            .AddReferences(MetadataFileReference typeof<System.Linq.Expressions.Expression>.Assembly.Location)
            .AddSyntaxTrees(syntaxTree)
            .WithOptions(CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))

    let diagnostics = csharpCompilation.GetDiagnostics() |> Seq.filter (fun diagnostic -> diagnostic.Severity = DiagnosticSeverity.Error)
    do diagnostics |> Seq.iter (fun d -> printfn "%A" d)

    do if not <| Seq.isEmpty diagnostics then
        "Failed to create compilation." |> failed

    /// Gets the name of the compilation.
    static member CompilationName = "TestCompilation"

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
        if assembly = null then
            use stream = new MemoryStream ()
            let emitResult = csharpCompilation.Emit stream

            if (emitResult.Success) then
                assembly <- stream.ToArray () |> Assembly.Load
            else
                emitResult.Diagnostics |> Seq.iter (fun diagnostic -> printf "%A" diagnostic)
                failed "Assembly compilation failed."

        assembly

    /// Finds the <see cref="TypeDeclarationSyntax" /> for the type with the given name in the compilation.
    /// Throws an exception if more than one type with the given name was found.
    member this.FindTypeDeclaration typeName =
        let displayFormat = SymbolDisplayFormat (SymbolDisplayGlobalNamespaceStyle.Omitted, SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces)
        let types = 
            this.SyntaxRoot
                .DescendantsAndSelf<BaseTypeDeclarationSyntax>()
                .Where(fun typeDeclaration -> 
                    let symbol = this.SemanticModel.GetDeclaredSymbol typeDeclaration
                    symbol.ToDisplayString displayFormat = typeName
                )
                .ToArray();

        if types.Length = 0 then
            sprintf "Found no type with name '%s'." typeName |> failed

        if types.Length > 1 then
            sprintf "Found more than one type with name '%s'." typeName |> failed

        types.[0]

    /// Finds the <see cref="ClassDeclarationSyntax" /> for the class with the given name in the compilation.
    /// Throws an exception if more than one class with the given name was found.
    member this.FindClassDeclaration className =
        match this.FindTypeDeclaration(className) with
        | :? ClassDeclarationSyntax as classDeclaration -> classDeclaration
        | _ -> sprintf "Found no class with name '%s'." className |> failed

    /// Finds the <see cref="InterfaceDeclarationSyntax" /> for the interface with the given name in the
    /// compilation. Throws an exception if more than one interface with the given name was found.
    member this.FindInterfaceDeclaration interfaceName =
        match this.FindTypeDeclaration(interfaceName) with
        | :? InterfaceDeclarationSyntax as interfaceDeclaration -> interfaceDeclaration
        | _ -> sprintf "Found no interface with name '%s'." interfaceName |> failed

    /// Finds the <see cref="MethodDeclarationSyntax" /> for the method with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or method with the given name was found.
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

    /// Finds the <see cref="VariableDeclaratorSyntax" /> for the field with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or field with the given name was found.
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

    /// Gets the <see cref="ITypeSymbol" /> representing the type with the given name.
    member this.FindTypeSymbol typeName =
        match csharpCompilation.GetTypeByMetadataName typeName with
        | null -> sprintf "Unable to find type with name %s" typeName |> failed
        | symbol -> symbol

    /// Gets the <see cref="ITypeSymbol" /> representing the class with given name.
    member this.FindClassSymbol className =
        match csharpCompilation.GetTypeByMetadataName className with
        | null -> sprintf "Unable to find class with name %s" className |> failed
        | symbol -> symbol

    /// Gets the <see cref="ITypeSymbol" /> representing the interface with the given name.
    member this.FindInterfaceSymbol interfaceName =
        match csharpCompilation.GetTypeByMetadataName interfaceName with
        | null -> sprintf "Unable to find interface with name %s" interfaceName |> failed
        | symbol -> symbol

    /// Gets the <see cref="IMethodSymbol" /> representing the method with the given name in the type with
    /// with the given name.
    member this.FindMethodSymbol typeName methodName =
        let typeSymbol = this.FindTypeSymbol typeName
        match typeSymbol.GetMembers(methodName).OfType<IMethodSymbol>() |> List.ofSeq with
        | [] -> sprintf "Unable to find method '%s' on type '%s'." methodName typeName |> failed
        | methodSymbol :: [] -> methodSymbol
        | _ -> sprintf "Found more than one method '%s' on type '%s'." methodName typeName |> failed

    /// Gets the <see cref="IFieldSymbol" /> representing the field with the given name in the type with
    /// the given name.
    member this.FindFieldSymbol typeName fieldName =
        let typeSymbol = this.FindTypeSymbol typeName
        match typeSymbol.GetMembers(fieldName).OfType<IFieldSymbol>() |> List.ofSeq with
        | [] -> sprintf "Unable to find field '%s' on type '%s'." fieldName typeName |> failed
        | methodSymbol :: [] -> methodSymbol
        | _ -> sprintf "Found more than one field '%s' on type '%s'." fieldName typeName |> failed

    /// If necessary, compiles the compilation and loads the resulting assembly into the app domain, then searches for
    /// a type with the given name and returns a new instance of the type by invoking the type's default constructor.
    member this.CreateObject<'T> typeName =
        match this.Compile().GetType(typeName) with
        | null -> sprintf "Unable to find a type with name '%s' in the compiled assembly." typeName |> failed
        | typeSymbol -> Activator.CreateInstance(typeSymbol) :?> 'T

    /// Checks whether the compilation has any diagnostics for the given diagnostic analyzer.
    member this.HasDiagnostics<'T when 'T : (new : unit -> 'T) and 'T :> IDiagnosticAnalyzer> () = 
        let analyzers = [| new 'T () :> IDiagnosticAnalyzer |]
        not <| AnalyzerDriver.GetDiagnostics(csharpCompilation, analyzers, new CancellationToken()).Any()