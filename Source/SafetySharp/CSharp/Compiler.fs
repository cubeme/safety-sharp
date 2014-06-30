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
open SafetySharp.CSharp.Diagnostics
open SafetySharp.CSharp.Normalization

/// The SafetySharp compiler that compiles C# code into a modeling assembly.
module Compiler =

    /// The version string of the compiler.
    [<Literal>]
    let Version = "0.0.1-beta"

    /// The file name of the modeling-time SafetySharp assembly.
    [<Literal>]
    let ModelingAssemblyFileName = "SafetySharp.Modeling.dll"

    /// The diagnostic analyzers that are used to diagnose the C# code before any normalizations.
    let diagnosticAnalyzers = 
        typeof<CSharpAnalyzer>.Assembly.GetTypes()
        |> Seq.where (fun typeInfo -> typeInfo.IsClass && not typeInfo.IsAbstract && typeof<CSharpAnalyzer>.IsAssignableFrom typeInfo)
        |> Seq.map (fun typeInfo -> (Activator.CreateInstance typeInfo) :?> IDiagnosticAnalyzer)

    /// Logs <paramref name="diagnostic" /> depending on its severity.
    let private logDiagnostic errorsOnly (diagnostic : Diagnostic) =
        match diagnostic.Severity with
        | DiagnosticSeverity.Error -> 
            Log.Error "%A" diagnostic
        | DiagnosticSeverity.Warning -> 
            if not errorsOnly then Log.Warn "%A" diagnostic
        | DiagnosticSeverity.Info -> 
            if not errorsOnly then Log.Info "%A" diagnostic
        | DiagnosticSeverity.Hidden -> 
            if not errorsOnly then Log.Debug "%A" diagnostic
        | _ -> Log.Die "Unknown C# diagnostic severity."

    /// Logs all <paramref name="diagnostics" /> depending on their severities. The function returns
    /// <c>false</c> when at least one error diagnostic has been reported.
    let private logDiagnostics errorsOnly (diagnostics : Diagnostic seq) =
        diagnostics |> Seq.iter (logDiagnostic errorsOnly)
        diagnostics |> Seq.exists (fun diagnostic -> diagnostic.Severity = DiagnosticSeverity.Error) |> not

    /// Instantiates a <see cref="Diagnostic" /> for the error and logs it.
    let private logError identifier message =
        Printf.ksprintf (fun message ->
            Diagnostic.Create (DiagnosticIdentifiers.Prefix + identifier, DiagnosticIdentifiers.Category, message, DiagnosticSeverity.Error, true, 0, false) 
            |> logDiagnostic true
        ) message

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
            Log.Die "%s: error: Assembly '%s' is not referenced." projectFile ModelingAssemblyFileName

        modelingAssembly

    /// Swaps out the referenced modeling-time SafetySharp assembly with the SafetySharp core assembly behind the
    /// modeler's back. This enables a couple of C# normalizations required for debugging, simulation and model
    /// transformations while only surfacing a minimal and convenient API for model creation. The function returns
    /// <c>None</c> when at least one error diagnostic has been reported after the assembly has been swapped.
    let private swapSafetySharpAssembly projectFile (compilation : Compilation) =
        let safetySharpAssembly = MetadataFileReference typeof<Component>.Assembly.Location
        let originalAssembly = getModelingAssemblyReference compilation projectFile
        let compilation = compilation.ReplaceReference (originalAssembly, safetySharpAssembly)

        if compilation.GetDiagnostics () |> logDiagnostics true then
            Some compilation
        else
            None

    /// Runs the SafetySharp diagnostic analyzers on the compilation, reporting all generated diagnostics. The function returns
    /// <c>false</c> when at least one error diagnostic has been reported.
    let private diagnose (compilation : Compilation) =
        if compilation.GetDiagnostics () |> logDiagnostics true then
            let diagnostics = AnalyzerDriver.GetDiagnostics (compilation, diagnosticAnalyzers, CancellationToken ()) |> Array.ofSeq
            diagnostics |> logDiagnostics false
        else
            false

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

    /// Applies the normalizer of type <typeparamref name="T" /> to the C# <paramref name="compilation" />.
    let private applyNormalizer<'T when 'T : (new : unit -> 'T) and 'T :> CSharpNormalizer> (compilation : Compilation) =
        let normalizer = new 'T ()
        normalizer.Normalize compilation

    /// Generates the modeling compilation units and adds them to the compilation.
    let private generateModelingCompilationUnits (compilation : Compilation) =
        let metadataCompilation = 
            compilation
            |> applyNormalizer<ChooseMethodNormalizer>

        outputCode metadataCompilation "obj/Model"
        addMetadata metadataCompilation compilation

    /// Applies normalizations to the simulation compilation.
    let private normalizeSimulationCode (compilation : Compilation) =
        let compilation =
            compilation
            |> applyNormalizer<ExternMethodNormalizer>

        outputCode compilation "obj/Simulation"
        compilation

    /// Performs the required normalization steps before the SafetySharp assembly is swapped and the code is split
    /// into the modeling compilation units and the simulation code.
    let private normalizeBeforeSwap (compilation : Compilation) =
        let compilation = 
            compilation
            |> applyNormalizer<UpdateMethodVisibilityNormalizer>
            |> applyNormalizer<ExpressionLifter>

        outputCode compilation "obj/BeforeSwap"
        compilation

    /// Overwrites the original assembly generated by the C# compiler with the assembly compiled from the rewritten code.
    let private emit assemblyPath (compilation : Compilation) =
        use ilStream = new FileStream (assemblyPath, FileMode.OpenOrCreate)
        use pdbStream = new FileStream (Path.ChangeExtension (assemblyPath, ".pdb"), FileMode.OpenOrCreate)
        let emitResult = compilation.Emit (ilStream, null, null, pdbStream)

        if emitResult.Success then
            0
        else
            emitResult.Diagnostics |> Seq.iter (logDiagnostic true)
            -1

    /// Compiles the C# modeling project identified by the given project file in the given configuration for the given platform.
    let Compile projectFile configuration platform =
        nullArg projectFile "projectFile"
        nullArg configuration "configuration"
        nullArg platform "platform"

        if not <| File.Exists projectFile then
            logError "0001" "Project file '%s' could not be found." projectFile
            -1
        elif String.IsNullOrWhiteSpace configuration then
            logError "0002" "Invalid project configuration: Configuration name cannot be the empty string."
            -1
        elif String.IsNullOrWhiteSpace platform then
            logError "0003" "Invalid compilation platform: Platform name cannot be the empty string."
            -1
        else
            let msBuildProperties = Dictionary<string, string> ()
            msBuildProperties.Add ("Configuration", configuration)
            msBuildProperties.Add ("Platform", platform)

            let workspace = MSBuildWorkspace.Create msBuildProperties
            let project = workspace.OpenProjectAsync(projectFile).Result

            let compilation = project.GetCompilationAsync().Result
            let diagnosticOptions = compilation.Options.SpecificDiagnosticOptions.Add("CS0626", ReportDiagnostic.Suppress)
            let options = compilation.Options.WithSpecificDiagnosticOptions diagnosticOptions
            let compilation = compilation.WithOptions options

            if not <| diagnose compilation then
                -1
            else
                match compilation |> normalizeBeforeSwap |> swapSafetySharpAssembly projectFile with
                | None -> -1
                | Some compilation -> 
                    compilation
                    |> generateModelingCompilationUnits
                    |> normalizeSimulationCode
                    |> emit project.OutputFilePath