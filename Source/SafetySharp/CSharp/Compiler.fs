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

open System
open System.Collections.Generic
open System.Linq
open System.IO
open System.Text
open System.Threading
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.Diagnostics
open Microsoft.CodeAnalysis.MSBuild
open SafetySharp.Modeling
open SafetySharp.Utilities

/// The SafetySharp compiler that compiles C# code into a modeling assembly.
module Compiler =

    /// The prefix that is used for all diagnostic identifiers.
    [<Literal>]
    let DiagnosticsPrefix = "SS";

    /// The category that is used for all diagnostics.
    [<Literal>]
    let DiagnosticsCategory = "SafetySharp";

    /// The version string of the compiler.
    [<Literal>]
    let Version = "0.0.1-beta";

    /// The file name of the modeling-time SafetySharp assembly.
    [<Literal>]
    let ModelingAssemblyFileName = "SafetySharp.Modeling.dll";

    /// Logs <paramref name="diagnostic" /> depending on its severity.
    let private logDiagnostic (diagnostic : Diagnostic) =
        match diagnostic.Severity with
        | DiagnosticSeverity.Error -> sprintf "%A" diagnostic |> Log.Error
        | DiagnosticSeverity.Warning -> sprintf "%A" diagnostic |> Log.Warn
        | DiagnosticSeverity.Info -> sprintf "%A" diagnostic |> Log.Info
        | DiagnosticSeverity.Hidden -> sprintf "%A" diagnostic |> Log.Debug
        | _ -> Log.Die "Unknown C# diagnostic severity."

    /// Instantiates a <see cref="Diagnostic" /> for the error and logs it.
    let private logError identifier message =
        Diagnostic.Create (DiagnosticsPrefix + identifier, DiagnosticsCategory, message, DiagnosticSeverity.Error, true, 0, true) 
        |> logDiagnostic 

    /// Writes the C# code contained in the <paramref name="compilation" /> to the directory denoted by
    /// <paramref name="path" />.
    let private outputCode (compilation : Compilation) path =
        #if DEBUG
        Directory.CreateDirectory path |> ignore

        compilation.SyntaxTrees
        |> Seq.iteri (fun index syntaxTree ->
            let fileName = Path.GetFileNameWithoutExtension (if syntaxTree.FilePath = null then String.Empty else syntaxTree.FilePath)
            let filePath = Path.Combine (path, sprintf "%s%i.cs" fileName index)

            File.WriteAllText (filePath, syntaxTree.GetText().ToString())
        )
        #else
        ()
        #endif

    /// Gets the reference to the modeling-time SafetySharp assembly used by the given compilation.
    let private getModelingAssemblyReference (compilation : Compilation) projectFile =
        let modelingAssembly =
            compilation.References.OfType<PortableExecutableReference>()
                .SingleOrDefault(fun reference -> Path.GetFileName reference.FullPath = ModelingAssemblyFileName)

        if modelingAssembly = null then
            sprintf "%s: error: Assembly '%s' is not referenced." projectFile ModelingAssemblyFileName |> Log.Die

        modelingAssembly

    /// Swaps out the referenced modeling-time SafetySharp assembly with the SafetySharp core assembly behind the
    /// modeler's back. This enables a couple of C# normalizations required for debugging, simulation and model
    /// transformations while only surfacing a minimal and convenient API for model creation.
    let private swapSafetySharpAssembly projectFile (compilation : Compilation) =
        let safetySharpAssembly = MetadataFileReference typeof<Component>.Assembly.Location
        let originalAssembly = getModelingAssemblyReference compilation projectFile
        compilation.ReplaceReference (originalAssembly, safetySharpAssembly)

    /// Runs the given diagnostic analyzers on the compilation, reporting all generated diagnostics. The function returns
    /// <c>false</c> when at least one error diagnostic has been reported.
    let private diagnose (compilation : Compilation) analyzers =
        let diagnostics = AnalyzerDriver.GetDiagnostics (compilation, analyzers, CancellationToken ()) |> Array.ofSeq
        diagnostics |> Array.iter logDiagnostic
        diagnostics |> Array.forall (fun diagnostic -> diagnostic.Severity <> DiagnosticSeverity.Error)

    /// Adds the metadata code to the simulation assembly.
    let private addMetadata (metadataCompilation : Compilation) (simulationCompilation : Compilation) =
        let attributeName = typeof<ModelingCompilationUnitAttribute>.FullName
        let csharpCode = StringBuilder ()

        metadataCompilation.SyntaxTrees |> Seq.iter (fun syntaxTree ->
            let content = syntaxTree.GetText().ToString().Trim().Replace("\"", "\"\"")
            let fileName = syntaxTree.FilePath.Replace("\\", "\\\\")

            csharpCode.AppendLine(String.Format("[assembly: {0}(@\"{1}\", \"{2}\")]", attributeName, content, fileName)) |> ignore
        )

        csharpCode.AppendLine(String.Format("[assembly: {0}(\"{1}\")]", typeof<ModelingAssemblyAttribute>.FullName, Version)) |> ignore
        simulationCompilation.AddSyntaxTrees(SyntaxFactory.ParseSyntaxTree(csharpCode.ToString()))

    /// Generates the modeling compilation units and adds them to the compilation.
    let private generateModelingCompilationUnits (compilation : Compilation) =
        let metadataCompilation = compilation
        // TODO

        outputCode metadataCompilation "obj/Model"
        addMetadata metadataCompilation compilation

    /// Applies normalizations to the simulation compilation.
    let private normalizeSimulationCode (compilation : Compilation) =
        // TODO

        outputCode compilation "obj/Simulation"
        compilation

    /// Overwrites the original assembly generated by the C# compiler with the assembly compiled from the rewritten code.
    let private emit assemblyPath (compilation : Compilation) =
        use ilStream = new FileStream (assemblyPath, FileMode.OpenOrCreate)
        use pdbStream = new FileStream (Path.ChangeExtension (assemblyPath, ".pdb"), FileMode.OpenOrCreate)
        let emitResult = compilation.Emit (ilStream, null, null, pdbStream)

        if emitResult.Success then
            0
        else
            emitResult.Diagnostics |> Seq.iter logDiagnostic
            -1

    /// Compiles the C# modeling project identified by the given project file in the given configuration for the given platform.
    let Compile projectFile configuration platform =
        Requires.NotNull projectFile "projectFile"
        Requires.NotNull configuration "configuration"
        Requires.NotNull platform "platform"

        if not <| File.Exists projectFile then
            sprintf "Project file '%s' could not be found." projectFile |> logError "0001"
            -1
        else if String.IsNullOrWhiteSpace configuration then
            "Invalid project configuration: Configuration name cannot be the empty string." |> logError "0002"
            -1
        else if String.IsNullOrWhiteSpace platform then
            "Invalid compilation platform: Platform name cannot be the empty string." |> logError "0003"
            -1
        else
            let msBuildProperties = Dictionary<string, string> ()
            msBuildProperties.Add ("Configuration", configuration)
            msBuildProperties.Add ("Platform", platform)

            let workspace = MSBuildWorkspace.Create msBuildProperties
            let project = workspace.OpenProjectAsync(projectFile).Result

            let compilation = project.GetCompilationAsync().Result

            if not <| diagnose compilation [] then
                -1
            else
                compilation
                |> swapSafetySharpAssembly projectFile
                |> generateModelingCompilationUnits
                |> normalizeSimulationCode
                |> emit project.OutputFilePath