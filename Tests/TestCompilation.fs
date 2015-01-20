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

[<AutoOpen>]
module RoslynTestHelper

open System
open System.Collections.Generic
open System.Collections.Immutable
open System.Linq
open System.IO
open System.Reflection
open System.Threading
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open Mono.Cecil
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn
open SafetySharp.Modeling

/// Raises when a C# compilation problem occurred.
type CompilationException (message : string) =
    inherit Exception (message)

/// Provides information about a diagnostic.
type Diagnostic =
    | Diagnostic of Identifier : string * Start : (int * int) * End : (int * int) * Message : string

/// Represents a compiled C# compilation unit with a single syntax tree.
[<AllowNullLiteral>]
type TestCompilation (csharpCode, [<ParamArray>] assemblies : Assembly array) =
    let mutable (assembly : Assembly) = null
    let failed message = Printf.ksprintf (fun message -> CompilationException message |> raise) message

    let compilationUnit = SyntaxFactory.ParseCompilationUnit ("using SafetySharp.Modeling; using SafetySharp.Modeling.CompilerServices;\n" + csharpCode)
    let syntaxTree = compilationUnit.SyntaxTree

    let assemblyPath = Path.Combine (Environment.CurrentDirectory, sprintf "tmp_%s.dll" (Guid.NewGuid().ToString ()))

    let csharpCompilation = 
        CSharpCompilation
            .Create(Path.GetFileNameWithoutExtension assemblyPath)
            .AddReferences(MetadataReference.CreateFromAssembly typeof<obj>.Assembly)
            .AddReferences(MetadataReference.CreateFromAssembly typeof<Component>.Assembly)
            .AddReferences(MetadataReference.CreateFromAssembly typeof<System.Linq.Expressions.Expression>.Assembly)
            .AddReferences(MetadataReference.CreateFromAssembly typeof<TestCompilation>.Assembly)
            .AddSyntaxTrees(syntaxTree)
            .WithOptions(CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary).WithOptimizationLevel OptimizationLevel.Release)

    let csharpCompilation =
        assemblies |> Array.fold (fun (c : CSharpCompilation) a -> c.AddReferences (MetadataReference.CreateFromFile a.Location)) csharpCompilation

    let rec addExternAliases (compilation : CSharpCompilation) (externAliases : (string * CSharpCompilation) list) =
        match externAliases with
        | [] -> compilation
        | (name, externCompilation) :: externAliases -> 
            let compilation = compilation.AddReferences(externCompilation.ToMetadataReference(ImmutableArray.Create(name)))
            addExternAliases compilation externAliases

    let diagnostics = csharpCompilation.GetDiagnostics() |> Seq.filter (fun diagnostic -> diagnostic.Severity = DiagnosticSeverity.Error)

    do if not <| Seq.isEmpty diagnostics then
        failed "Failed to create compilation:\n%s\n\n%s" (diagnostics |> Seq.fold (fun s d -> sprintf "%s\n%A" s d) "") csharpCode

    /// Gets the syntax tree of the compilation.
    member this.SyntaxTree = syntaxTree

    /// Gets the <see cref="CSharpCompilation" /> corresponding to the current instance.
    member this.CSharpCompilation : CSharpCompilation = csharpCompilation

    /// Gets the root syntax node of the syntax tree.
    member this.SyntaxRoot = syntaxTree.GetRoot ()

    /// Gets the semantic model for the compilation's syntax tree.
    member this.SemanticModel = csharpCompilation.GetSemanticModel syntaxTree

    /// Emits an in-memory assembly for the compilation and loads the assembly into the app domain.
    member this.Compile () =
        if assembly = null then
            // Create a temporary file and load the assembly from the file, as some
            // tests require the assembly to be present on the file system
            let emitResult = csharpCompilation.Emit (assemblyPath, (Path.ChangeExtension (assemblyPath, "pdb")))

            if (emitResult.Success) then
                assembly <- Assembly.LoadFile assemblyPath
            else
                emitResult.Diagnostics |> Seq.iter (fun diagnostic -> printf "%A" diagnostic)
                failed "Assembly compilation failed."

        assembly

    /// Emits an in-memory assembly for the compilation and returns a Mono.Cecil assembly definition for the compiled assembly.
    member this.GetAssemblyDefinition () =
        use stream = new MemoryStream ()
        let emitResult = csharpCompilation.Emit stream

        if (emitResult.Success) then
            stream.Seek (0L, SeekOrigin.Begin) |> ignore
            AssemblyDefinition.ReadAssembly stream
        else
            emitResult.Diagnostics |> Seq.iter (fun diagnostic -> printf "%A" diagnostic)
            failed "Assembly compilation failed."
            null

    /// Finds the <see cref="TypeDeclarationSyntax" /> for the type with the given name in the compilation.
    /// Throws an exception if more than one type with the given name was found.
    member this.FindTypeDeclaration typeName =
        let displayFormat = SymbolDisplayFormat (SymbolDisplayGlobalNamespaceStyle.Omitted, SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces)
        let types = 
            this.SyntaxRoot.DescendantsAndSelf<BaseTypeDeclarationSyntax> ()
            |> Seq.where (fun typeDeclaration -> 
                    let symbol = this.SemanticModel.GetDeclaredSymbol typeDeclaration
                    symbol.ToDisplayString displayFormat = typeName
                )
            |> List.ofSeq
                
        match types with
        | typeDeclaration :: [] -> typeDeclaration
        | [] -> failed "Found no type with name '%s'." typeName
        | _ -> failed "Found more than one type with name '%s'." typeName

    /// Finds the <see cref="ClassDeclarationSyntax" /> for the class with the given name in the compilation.
    /// Throws an exception if more than one class with the given name was found.
    member this.FindClassDeclaration className =
        match this.FindTypeDeclaration(className) with
        | :? ClassDeclarationSyntax as classDeclaration -> classDeclaration
        | _ -> failed "Found no class with name '%s'." className

    /// Finds the <see cref="InterfaceDeclarationSyntax" /> for the interface with the given name in the
    /// compilation. Throws an exception if more than one interface with the given name was found.
    member this.FindInterfaceDeclaration interfaceName =
        match this.FindTypeDeclaration(interfaceName) with
        | :? InterfaceDeclarationSyntax as interfaceDeclaration -> interfaceDeclaration
        | _ -> failed "Found no interface with name '%s'." interfaceName

    /// Finds the <see cref="MethodDeclarationSyntax" /> for the method with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or method with the given name was found.
    member this.FindMethodDeclaration typeName methodName =
        let methods = 
            this.FindTypeDeclaration(typeName).DescendantsAndSelf<MethodDeclarationSyntax> ()
            |> Seq.where (fun methodDeclaration -> methodDeclaration.Identifier.ValueText = methodName)
            |> List.ofSeq

        match methods with
        | methodDeclaration :: [] -> methodDeclaration
        | [] -> failed "Found no methods with name '%s' in '%s'." methodName typeName
        | _ -> failed "Found more than one method with name '%s' in '%s'." methodName typeName

    /// Finds the <see cref="PropertyDeclarationSyntax" /> for the property with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or property with the given name was found.
    member this.FindPropertyDeclaration typeName propertyName =
        let properties = 
            this.FindTypeDeclaration(typeName).DescendantsAndSelf<PropertyDeclarationSyntax> ()
            |> Seq.where (fun propertyDeclaration -> propertyDeclaration.Identifier.ValueText = propertyName)
            |> List.ofSeq

        match properties with
        | propertyDeclaration :: [] -> propertyDeclaration
        | [] -> failed "Found no properties with name '%s' in '%s'." propertyName typeName
        | _ -> failed "Found more than one property with name '%s' in '%s'." propertyName typeName

    /// Finds the <see cref="VariableDeclaratorSyntax" /> for the field with the given name in the type with the given name
    /// within the compilation. Throws an exception if more than one type or field with the given name was found.
    member this.FindFieldDeclaration typeName fieldName =
        let fields = 
            this.FindTypeDeclaration(typeName).DescendantsAndSelf<FieldDeclarationSyntax> ()
            |> Seq.collect (fun fieldDeclaration -> fieldDeclaration.Declaration.Variables :> IEnumerable<VariableDeclaratorSyntax>)
            |> Seq.filter (fun variableDeclaration -> variableDeclaration.Identifier.ValueText = fieldName)
            |> List.ofSeq

        match fields with
        | fieldDeclaration :: [] -> fieldDeclaration
        | [] -> failed "Found no fields with name '%s' in '%s'." fieldName typeName
        | _ -> failed "Found more than one field with name '%s' in '%s'." fieldName typeName

    /// Gets the <see cref="VariableDeclaratorSyntax" /> instances representing the local variables with the given name in the method
    /// with the given name in the type with the given name.
    member this.FindLocalDeclarations typeName methodName localName =
        let methodDeclaration = this.FindMethodDeclaration typeName methodName
        methodDeclaration.Descendants<VariableDeclaratorSyntax> ()
        |> Seq.where (fun declarator -> declarator.Identifier.ValueText = localName)
        |> List.ofSeq
    
    /// Gets the <see cref="VariableDeclaratorSyntax" /> representing the local variable with the given name in the method
    /// with the given name in the type with the given name.
    member this.FindLocalDeclaration typeName methodName localName =
        match this.FindLocalDeclarations typeName methodName localName with 
        | localDeclaration :: [] -> localDeclaration
        | [] -> failed "Found no local with name '%s' in method '%s.%s'." localName typeName methodName
        | _ -> failed "Found more than one local with name '%s' in method '%s.%s'." localName typeName methodName

    /// Gets the <see cref="ITypeSymbol" /> representing the type with the given name.
    member this.FindTypeSymbol typeName =
        match csharpCompilation.GetTypeByMetadataName typeName with
        | null -> failed "Unable to find type with name %s" typeName
        | symbol -> symbol

    /// Gets the <see cref="ITypeSymbol" /> representing the class with given name.
    member this.FindClassSymbol className =
        match csharpCompilation.GetTypeByMetadataName className with
        | null -> failed "Unable to find class with name %s" className
        | symbol -> symbol

    /// Gets the <see cref="ITypeSymbol" /> representing the interface with the given name.
    member this.FindInterfaceSymbol interfaceName =
        match csharpCompilation.GetTypeByMetadataName interfaceName with
        | null -> failed "Unable to find interface with name %s" interfaceName
        | symbol -> symbol

    /// Gets the <see cref="IMethodSymbol" /> representing the method with the given name in the type with
    /// with the given name.
    member this.FindMethodSymbol typeName methodName =
        let typeSymbol = this.FindTypeSymbol typeName
        match typeSymbol.GetMembers(methodName).OfType<IMethodSymbol> () |> List.ofSeq with
        | methodSymbol :: [] -> methodSymbol
        | [] -> failed "Unable to find method '%s' on type '%s'." methodName typeName
        | _ -> failed "Found more than one method '%s' on type '%s'." methodName typeName

    /// Gets the <see cref="IPropertySymbol" /> representing the property with the given name in the type with
    /// with the given name.
    member this.FindPropertySymbol typeName propertyName =
        let typeSymbol = this.FindTypeSymbol typeName
        match typeSymbol.GetMembers(propertyName).OfType<IPropertySymbol> () |> List.ofSeq with
        | propertySymbol :: [] -> propertySymbol
        | [] -> failed "Unable to find property '%s' on type '%s'." propertyName typeName
        | _ -> failed "Found more than one property '%s' on type '%s'." propertyName typeName

    /// Gets the <see cref="IFieldSymbol" /> representing the field with the given name in the type with
    /// the given name.
    member this.FindFieldSymbol typeName fieldName =
        let typeSymbol = this.FindTypeSymbol typeName
        match typeSymbol.GetMembers(fieldName).OfType<IFieldSymbol> () |> List.ofSeq with
        | methodSymbol :: [] -> methodSymbol
        | [] -> failed "Unable to find field '%s' on type '%s'." fieldName typeName
        | _ -> failed "Found more than one field '%s' on type '%s'." fieldName typeName

    /// Gets the <see cref="IParameterSymbol" /> representing the parameter with the given name in the method
    /// with the given name in the type with the given name.
    member this.FindParameterSymbol typeName methodName parameterName =
        let methodSymbol = this.FindMethodSymbol typeName methodName
        match methodSymbol.Parameters |> Seq.where (fun parameter -> parameter.Name = parameterName) |> List.ofSeq with
        | parameterSymbol :: [] -> parameterSymbol
        | [] -> failed "Unable to find parameter '%s' of method '%s.%s'." parameterName typeName methodName
        | _ -> failed "Found more than one parameter '%s' of method '%s.%s'." parameterName typeName methodName

    /// Gets the <see cref="ILocalSymbol" /> representing the local variable with the given name in the method
    /// with the given name in the type with the given name.
    member this.FindLocalSymbols typeName methodName localName =
        this.FindLocalDeclarations typeName methodName localName
        |> List.map (fun localDeclaration -> this.SemanticModel.GetDeclaredSymbol localDeclaration :?> ILocalSymbol)

    /// Gets the <see cref="ILocalSymbol" /> representing the local variable with the given name in the method
    /// with the given name in the type with the given name.
    member this.FindLocalSymbol typeName methodName localName =
        let localDeclaration = this.FindLocalDeclaration typeName methodName localName
        this.SemanticModel.GetDeclaredSymbol localDeclaration :?> ILocalSymbol

    /// If necessary, compiles the compilation and loads the resulting assembly into the app domain, then searches for
    /// a type with the given name and returns a new instance of the type by invoking the type's default constructor.
    member this.CreateObject<'T> typeName =
        match this.Compile().GetType(typeName) with
        | null -> failed "Unable to find a type with name '%s' in the compiled assembly." typeName
        | typeSymbol -> Activator.CreateInstance(typeSymbol) :?> 'T

    /// Checks whether the given C# code has any diagnostics.
    static member GetDiagnostic (analyzer : DiagnosticAnalyzer) csharpCode =
        let compilation = TestCompilation csharpCode
        let options = AnalyzerOptions (Enumerable.Empty<AdditionalStream> (), Dictionary<string, string> ())
        let analyzer = ImmutableArray.Create analyzer

        // TODO: Use Compilation.GetDiagnosticsAsync instead once available
        let mutable compilation = compilation.CSharpCompilation :> Compilation
        let analyzerDriver = AnalyzerDriver.Create (compilation, analyzer, options, &compilation, CancellationToken ())
        compilation.GetDiagnostics () |> ignore
        let diagnostics = analyzerDriver.GetDiagnosticsAsync().Result

        if diagnostics.Length > 1 then
            raise (CompilationException (sprintf "More than one diagnostic has been emitted: %s" (String.Join(Environment.NewLine, diagnostics))))
        elif diagnostics.Length = 0 then
            None
        else
            let diagnostic = diagnostics.[0]
            let span = diagnostic.Location.GetLineSpan ()
            Diagnostic (diagnostic.Id, 
                        (span.StartLinePosition.Line, span.StartLinePosition.Character),
                        (span.EndLinePosition.Line, span.EndLinePosition.Character),
                        diagnostic.GetMessage ())
            |> Some

    /// Normalizes the code using the given normalizer and returns the code of the first class contained in the given code.
    static member GetNormalizedSyntaxTree (normalizer : CSharpNormalizer) csharpCode =
        let compilation = TestCompilation csharpCode
        normalizer.Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()

    /// Normalizes the code using the given normalizer and returns the code of the first class contained in the given code.
    static member GetNormalizedSyntaxTreeWithExternAliases (normalizer : CSharpNormalizer) csharpCode externAliases =
        let compilation = TestCompilation (csharpCode, externAliases |> Array.ofList)
        normalizer.Normalize(compilation.CSharpCompilation).SyntaxTrees.Single ()

    /// Normalizes the code using the given normalizer and returns the code of the first class contained in the given code.
    static member GetNormalizedClass (normalizer : CSharpNormalizer) csharpCode =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree normalizer csharpCode
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    /// Normalizes the code using the given normalizer and returns the code of the first class contained in the given code.
    static member GetNormalizedClassWithExternAliases (normalizer : CSharpNormalizer) csharpCode externAliases =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTreeWithExternAliases normalizer csharpCode externAliases
        syntaxTree.Descendants<ClassDeclarationSyntax>().Single().ToFullString ()

    /// Normalizes the code using the given normalizer and returns the code of the first interface contained in the given code.
    static member GetNormalizedInterface (normalizer : CSharpNormalizer) csharpCode =
        let syntaxTree = TestCompilation.GetNormalizedSyntaxTree normalizer csharpCode
        syntaxTree.Descendants<InterfaceDeclarationSyntax>().Single().ToFullString ()