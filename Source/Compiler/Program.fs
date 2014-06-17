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

open SafetySharp.Utilities

open System
open CommandLine
open CommandLine.Text
open SafetySharp.CSharp

/// Provides access to the command line arguments that have been provided to the compiler.
type CommandLineArguments () =
    /// Gets or sets the name of the configuration that should be used to compile the project.
    [<Option("configuration", Required = true, HelpText = "The name of the configuration that should be used to compile the project.")>]
    member val Configuration = "" with get, set

    /// <summary>
    ///     Gets or sets the name of the platform that should be used to compile the project.
    /// </summary>
    [<Option("platform", Required = true, HelpText = "The name of the platform that should be used to compile the project.")>]
    member val Platform = "" with get, set

    /// <summary>
    ///     Gets or sets the path to the C# project file that should be compiled.
    /// </summary>
    [<Option("project", Required = true, HelpText = "The path to the C# project file that should be compiled.")>]
    member val ProjectFile = "" with get, set

    /// <summary>
    ///     Gets or sets a value indicating whether all compiler output should be suppressed.
    /// </summary>
    [<Option("silent", Required = false, HelpText = "Suppresses all compiler output except for errors and warnings.")>]
    member val Silent = false with get, set

    /// <summary>
    ///     Generates a help message about the correct usage of the compiler's command line arguments.
    /// </summary>
    [<HelpOption('h', "help")>]
    member this.GenerateHelpMessage () =
        let help = 
            new HelpText (
                AdditionalNewLineAfterOption = true,
                AddDashesToOption = true
            )

        help.AddOptions this
        help.ToString ()

/// The command line arguments that have been used to invoke the compiler.
let private arguments = new CommandLineArguments ()

/// Wires up the <see cref="Log.Logged" /> event to write all logged messages to the console.
let private printToConsole logEntry =
    let writeToConsole color message =
        Console.ForegroundColor <- color
        Console.WriteLine (message : string)
        Console.ResetColor ()

    match logEntry.Type with
    | Debug ->
        if not arguments.Silent then
            writeToConsole ConsoleColor.Magenta logEntry.Message
    | Info ->
        if not arguments.Silent then
            writeToConsole ConsoleColor.White logEntry.Message
    | Warning ->
        writeToConsole ConsoleColor.Yellow logEntry.Message
    | Error ->
        writeToConsole ConsoleColor.Red logEntry.Message
    | Fatal ->
        writeToConsole ConsoleColor.Red logEntry.Message

/// The entry point to the compiler.
[<EntryPoint>]
let main args = 
    Log.Logged.Add printToConsole

    use parser = new Parser(fun c -> c.HelpWriter <- null)
    
    // Check the arguments for '--help' or '-h' as the command line parser library handles help in a strange
    // way. If so, output the help screen and successfully terminate the application.
    if args |> Seq.exists (fun arg -> arg = "--help" || arg = "-h") then
        Log.Info "%s" <| arguments.GenerateHelpMessage ()
        0
    // If there was an error parsing the command line, show the help screen and terminate the application.
    else if not <| parser.ParseArguments (args, arguments) then
        arguments.Silent <- false;
        Log.Info "%s" <| arguments.GenerateHelpMessage ()
        Log.Die "Invalid command line arguments."
        -1
    else
        Log.Info ""

        Log.Info "SafetySharp Compiler"
        Log.Info "Copyright (c) 2014 Institute for Software & Systems Engineering"

        Log.Info ""
        Log.Info "This is free software. You may redistribute copies of it under the terms of"
        Log.Info "the MIT license (see http://opensource.org/licenses/MIT)."

        Log.Info ""

        // We're finally ready to start the compilation process...
        try
            let resultCode = Compiler.Compile arguments.ProjectFile arguments.Configuration arguments.Platform
            if resultCode = 0 then
                Log.Info "Compilation completed successfully."

            resultCode
        with 
        | e ->
            Log.Error "A fatal compilation error occurred: %s" e.Message
            Log.Info "%s" e.StackTrace
            -1;
