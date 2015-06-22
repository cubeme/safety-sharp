// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Analysis.Modelchecking.NuXmv


module internal NuXmvCommandsToString =
    open NuXmvToString

    let exportNameOfEnvironmentVariable (variable:IEnvironmentVariable) : string =
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

    let exportNuSMVCommand (command:NuSMVCommand) : string =
        match command with
            | NuSMVCommand.ReadModel (fileName:string) ->
                 sprintf "read_model -i %s" fileName
            | NuSMVCommand.FlattenHierarchy ->
                "flatten_hierarchy"
            | NuSMVCommand.ShowVars -> "show_vars"
            | NuSMVCommand.ShowDependencies (expression:NextExpression) ->
                sprintf "show_dependencies -e %s" (exportNextExpression expression)
            | NuSMVCommand.EncodeVariables ->
                "encode_variables"
            | NuSMVCommand.BuildModel ->
                "build_model"
            | NuSMVCommand.Go ->
                "go"
            | NuSMVCommand.BuildFlatModel ->
                "build_flat_model"

            | NuSMVCommand.CheckFsm ->
                "check_fsm"
            | NuSMVCommand.CheckCtlSpec (formula:CtlExpression) ->
                sprintf "check_ctlspec -p \"%s\"" (exportCtlExpression formula)
            | NuSMVCommand.CheckInvar (formula:NextExpression) ->
                sprintf "check_invar -p \"%s\"" (exportNextExpression formula)
            | NuSMVCommand.CheckLtlSpec (formula:LtlExpression) ->
                sprintf "check_ltlspec -p \"%s\"" (exportLtlExpression formula)
            //| NuSMVCommand.CheckCompute  ->
            //    ""
            | NuSMVCommand.CheckProperty (name:string) ->
                sprintf "check_property -P \"%s\"" name
            | NuSMVCommand.AddPropertyCtl (name:string,formula:CtlExpression) ->
                sprintf "add_property -c -p \"%s\" -n \"%s\"" (exportCtlExpression formula) name
            | NuSMVCommand.AddPropertyInvar (name:string,formula:NextExpression) ->
                sprintf "add_property -i -p \"%s\" -n \"%s\"" (exportNextExpression formula) name
            | NuSMVCommand.AddPropertyLtl (name:string,formula:LtlExpression) ->
                sprintf "add_property -l -p \"%s\" -n \"%s\"" (exportLtlExpression formula) name
            //| NuSMVCommand.AddPropertyCompute (name:string,formula:LtlExpression) ->
            //    sprintf "add_property -q -p \"%s\" -n \"%s\"" (exportCtlExpression formula) name

            //| NuSMVCommand.AddPropertyPsl (name:string,formula) ->
            //    sprintf "add_property -s -p \"%s\" -n \"%s\"" (exportCtlExpression formula) name

            | NuSMVCommand.Echo (variable:string) ->
                sprintf "echo %s" variable
            | NuSMVCommand.EchoTyped (variable:IEnvironmentVariable) ->
                sprintf "echo %s" (exportNameOfEnvironmentVariable variable)
            | NuSMVCommand.PrintUsage ->
                "print_usage"
            | NuSMVCommand.Quit ->
                "quit"
            | NuSMVCommand.Reset ->
                "reset"
            | NuSMVCommand.Set (name:string,value:string option) ->
                let valueStr =
                    match value with
                        | Some(value) ->
                            if value.Contains(" ") then
                                sprintf " \"%s\"" value //add quotation marks
                            else
                                sprintf " %s" value
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
                sprintf "unset %s" (exportNameOfEnvironmentVariable variable)
            | NuSMVCommand.Usage ->
                "usage"

    let exportNuXmvCommand (command:NuXmvCommand) : string =
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

    let exportCustomCommand (command:NuXmvCustomCommand) : string =
        command.Command
    
    let exportICommand (command:ICommand) : string =
        match command with
            | :? NuXmvCustomCommand as command -> exportCustomCommand command
            | :? NuXmvStartedCommand as command -> "NuXmv Started"
            | :? NuSMVCommand as command -> exportNuSMVCommand command
            | :? NuXmvCommand as command -> exportNuXmvCommand command
            | _ -> failwith "NotImplementedYet"

    let exportNuXmvCommandLineArgument (argument:NuXmvCommandLine) : string =
        match argument with
            | NuXmvCommandLine.Help                        -> "-help"
            | NuXmvCommandLine.Verbose                     -> "-v 1"
            | NuXmvCommandLine.Interactive                 -> "-int"
            | NuXmvCommandLine.AvoidLoadingDefaultSettings -> "-s"

    let exportNuXmvCommandLine (arguments:NuXmvCommandLine list) : string =
        arguments |> List.map (fun argument -> exportNuXmvCommandLineArgument argument)
                  |> String.concat " "