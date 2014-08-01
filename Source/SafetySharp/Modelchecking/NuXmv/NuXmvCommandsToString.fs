﻿// The MIT License (MIT)
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

namespace SafetySharp.Internal.Modelchecking.NuXmv


type internal ExportCommandsToString() =
    
    let astToFile = ExportNuXmvAstToFile()

    member this.ExportNameOfEnvironmentVariable (variable:IEnvironmentVariable) : string =
        match variable with
            // NuSMV
            | :? NuSMVEnvironmentVariables.NusmvStdErr as stderr -> "nusmv_stderr"
            | :? NuSMVEnvironmentVariables.NusmvStdout as stdout -> "nusmv_stdout"
            | :? NuSMVEnvironmentVariables.NusmvStdIn as stdin -> "nusmv_stdin"
            | :? NuSMVEnvironmentVariables.DefaultTracePlugin as tracePlugin -> "default_trace_plugin"
            // NuXmv
            | :? NuXmvEnvironmentVariables.AbstractionEngine as abstractionEngine -> "abstraction.engine"
            // NotImplementedYet
            | _ -> failwith "NotImplementedYet"

    member this.ExportNuSMVCommand (command:NuSMVCommand) : string =
        match command with
            | NuSMVCommand.ReadModel (fileName:string) ->
                 sprintf "read_model -i %s" fileName
            | NuSMVCommand.FlattenHierarchy ->
                "flatten_hierarchy"
            | NuSMVCommand.ShowVars -> "show_vars"
            | NuSMVCommand.ShowDependencies (expression:NextExpression) ->
                sprintf "show_dependencies -e %s" (astToFile.ExportNextExpression expression)
            | NuSMVCommand.EncodeVariables ->
                "encode_variables"
            | NuSMVCommand.BuildModel ->
                "build_model"
            | NuSMVCommand.Go ->
                "go"
            | NuSMVCommand.BuildFlatModel ->
                "build_flat_model"
                
            | NuSMVCommand.Echo (variable:string) ->
                sprintf "echo %s" variable
            | NuSMVCommand.EchoTyped (variable:IEnvironmentVariable) ->
                sprintf "echo %s" (this.ExportNameOfEnvironmentVariable variable)
            | NuSMVCommand.PrintUsage ->
                "print_usage"
            | NuSMVCommand.Quit ->
                "quit"
            | NuSMVCommand.Reset ->
                "reset"
            | NuSMVCommand.Set (name:string,value:string option) ->
                let valueStr =
                    match value with
                        | Some(value) -> sprintf " %s" value
                        | None -> ""
                sprintf "set %s%s" name valueStr
            
            | NuSMVCommand.SetTyped (variable:IEnvironmentVariable)  ->
                match variable with
                    // NuSMV
                    | :? NuSMVEnvironmentVariables.NusmvStdErr as stderr ->
                        sprintf "set nusmv_stderr %s" stderr.FileName
                    | :? NuSMVEnvironmentVariables.NusmvStdout as stdout ->
                        sprintf "set nusmv_stdout %s" stdout.FileName
                    | :? NuSMVEnvironmentVariables.NusmvStdIn as stdin ->
                        sprintf "set nusmv_stdin %s" stdin.FileName
                    | :? NuSMVEnvironmentVariables.DefaultTracePlugin as tracePlugin ->
                        match tracePlugin with
                            | NuSMVEnvironmentVariables.DefaultTracePlugin.BasicChangesOnly -> "set default_trace_plugin 0"
                            | NuSMVEnvironmentVariables.DefaultTracePlugin.BasicAll -> "set default_trace_plugin 1"
                            | NuSMVEnvironmentVariables.DefaultTracePlugin.Xml -> "set default_trace_plugin 4"
                    // NuXmv
                    | :? NuXmvEnvironmentVariables.AbstractionEngine as abstractionEngine ->
                        let engine = match abstractionEngine with
                                        | NuXmvEnvironmentVariables.AbstractionEngine.Msat -> "msat"
                                        | NuXmvEnvironmentVariables.AbstractionEngine.Structural -> "structural"
                                        | NuXmvEnvironmentVariables.AbstractionEngine.Hybrid -> "hybrid"
                                        | NuXmvEnvironmentVariables.AbstractionEngine.Bdd -> "bdd"
                        sprintf "set abstraction.engine %s" engine
                    // NotImplementedYet
                    | _ -> failwith "NotImplementedYet"
            | NuSMVCommand.GetAllEnvironmentalVariables ->
                "set" // Set without parameters
            
            | NuSMVCommand.Unset (name:string) ->
                sprintf "unset %s" name
            
            | NuSMVCommand.UnsetTyped (variable:IEnvironmentVariable)  ->
                sprintf "unset %s" (this.ExportNameOfEnvironmentVariable variable)
            | NuSMVCommand.Usage ->
                "usage"

    member this.ExportNuXmvCommand (command:NuXmvCommand) : string =
        match command with
            | NuXmvCommand.MsatPickState             -> failwith "NotImplementedYet"
            | NuXmvCommand.MsatSimulate              -> failwith "NotImplementedYet"

            | NuXmvCommand.MsatCheckInvarBmc         -> failwith "NotImplementedYet"
            | NuXmvCommand.CheckInvarBmcItp          -> failwith "NotImplementedYet"
            | NuXmvCommand.CheckInvarIc3             -> failwith "NotImplementedYet"

            | NuXmvCommand.MsatCheckLtlspecBmc       -> failwith "NotImplementedYet"
            | NuXmvCommand.CheckLtlspecKlive         -> failwith "NotImplementedYet"
            | NuXmvCommand.CheckLtlspecSimplify      -> failwith "NotImplementedYet"
            | NuXmvCommand.CheckLtlspecCompositional -> failwith "NotImplementedYet"

            | NuXmvCommand.WriteSimplifiedModelRel   -> failwith "NotImplementedYet"
            | NuXmvCommand.WriteSimplifiedModelFunc  -> failwith "NotImplementedYet"
            | NuXmvCommand.BuildSimplifiedProperty   -> failwith "NotImplementedYet"

    member this.ExportCustomCommand (command:NuXmvCustomCommand) : string =
        command.Command
    
    member this.ExportICommand (command:ICommand) : string =
        match command with
            | :? NuXmvCustomCommand as command -> this.ExportCustomCommand command
            | :? NuSMVCommand as command -> this.ExportNuSMVCommand command
            | :? NuXmvCommand as command -> this.ExportNuXmvCommand command
            | _ -> failwith "NotImplementedYet"

    member this.ExportNuXmvCommandLineArgument (argument:NuXmvCommandLine) : string =
        match argument with
            | NuXmvCommandLine.Help                        -> "-help"
            | NuXmvCommandLine.Verbose                     -> "-v 1"
            | NuXmvCommandLine.Interactive                 -> "-int"
            | NuXmvCommandLine.AvoidLoadingDefaultSettings -> "-s"

    member this.ExportNuXmvCommandLine (arguments:NuXmvCommandLine list) : string =
        arguments |> List.map (fun argument -> this.ExportNuXmvCommandLineArgument argument)
                  |> String.concat " "