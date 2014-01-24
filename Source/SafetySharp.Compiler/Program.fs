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

// ======================================================================================================================================
// Assembly Metadata
// ======================================================================================================================================

/// Provides metadata for the assembly.
module internal AssemblyMetadata =
    open System
    open System.Diagnostics
    open System.Reflection
    open CommandLine

    [<assembly: AssemblyTitle ("Safety Sharp Compiler 0.1dev")>]
    [<assembly: AssemblyCopyright ("Copyright (c) 2014 Institute for Software & Systems Engineering")>]
    [<assembly: AssemblyVersion ("0.1.0.0")>]
    [<assembly: AssemblyFileVersion ("0.1.0.0")>]
    [<assembly: AssemblyCompany ("Institute for Software & Systems Engineering")>]
    [<assembly: AssemblyLicense ("This is free software. You may redistribute copies of it under the terms of",
        "the MIT license (see http://opensource.org/licenses/MIT).")>]

    do ()

    /// Gets the value of an assembly metadata attribute.
    let private getMetadata<'a when 'a :> Attribute and 'a : null and 'a : equality> (selector : 'a -> string) =
        let assembly = Assembly.GetExecutingAssembly ()
        let attribute = assembly.GetCustomAttribute<'a> ()

        Debug.Assert (attribute <> null, sprintf "Attribute '%s' could not be found." typeof<'a>.FullName)
        selector attribute

    /// The name of the assembly.
    let internal Name = 
        getMetadata<AssemblyTitleAttribute> (fun attribute -> attribute.Title)

    /// The copyright information of the assembly.
    let internal Copyright = 
        getMetadata<AssemblyCopyrightAttribute> (fun attribute -> attribute.Copyright)

    /// The license information of the assembly.
    let internal License = 
        getMetadata<AssemblyLicenseAttribute> (fun attribute -> attribute.Line1 + Environment.NewLine + attribute.Line2)

// ======================================================================================================================================
// Entry Point and Command Line Options
// ======================================================================================================================================

// This module should be internal - however, it must be public for the command line parser library to work.
module (* internal *) Program =
    open System
    open CommandLine
    open CommandLine.Text

    /// Provides access to the command line options the compiler has been invoked with.
    type Options() =
        /// Gets the path to the project file that should be compiled.
        [<Option('p', "Project", HelpText = "The path to the project file that should be compiled.")>]
        member val Project = String.Empty with get, set

        /// Generates a help message about the correct usage of the compiler if any command line parsing errors occurred.
        [<HelpOption>]
        member this.GetUsage () =
            let help = HelpText ()
            help.AdditionalNewLineAfterOption <- true
            help.AddDashesToOption <- true

            help.AddPreOptionsLine("Invalid command line parameters.");
            help.AddOptions(this)
            help.ToString()

    /// The entry point of the compiler when invoked via the command line.
    [<EntryPoint>]
    let private main args = 
        printfn ""

        printfn "%s" AssemblyMetadata.Name
        printfn "%s" AssemblyMetadata.Copyright

        printfn ""
        printfn "%s" AssemblyMetadata.License
        printfn ""

        let options = Options ()
        use parser = new Parser (new Action<ParserSettings> (fun c -> c.HelpWriter <- Console.Out))
        if parser.ParseArguments (args, options) then
            printfn "Project: %s" options.Project

        printfn ""

        0
