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

namespace SafetySharp.Internal.Modelchecking.NuXmv

type internal IEnvironmentVariable =
    interface end

type internal ICommand =
    interface end

// Chapter 4

// Note: We only introduce commands, which might be useful for us

[<RequireQualifiedAccess>]
type internal NuSMVCommand =
    // Chapter 4.1 Model Reading and Building
    | ReadModel of FileName:string
    | FlattenHierarchy
    | ShowVars
    | ShowDependencies of Expression:NextExpression
    | EncodeVariables
    | BuildModel
    | Go
    | BuildFlatModel
    // Chapter 4.2 Commands for Checking Specifications
    // Chapter 4.3 Commands for Bounded Model Checking
    // Chapter 4.4 Commands for checking PSL specifications
    // Chapter 4.5 Simulation Commands
    // Chapter 4.6 Execution Commands
    // Chapter 4.7 Traces
    // Chapter 4.8 Trace Plugins
    // Chapter 4.9 Interface to the DD Package
    // Chapter 4.10 Administration Commands
    | Echo of Variable:string
    | EchoTyped of Variable:IEnvironmentVariable // Typed version of "Echo" for convenience
    | PrintUsage
    | Quit
    | Reset
    | Set of Name:string * Value:(string option)
    | SetTyped of IEnvironmentVariable // Typed version of "Set" for convenience
    | GetAllEnvironmentalVariables // Set without parameters
    | Unset of Name:string
    | UnsetTyped of IEnvironmentVariable
    | Usage
    with interface ICommand

// Chapter 4.11 Other Environment Variables
module internal NuSMVEnvironmentVariables =    
    [<RequireQualifiedAccess>]
    type NusmvStdErr = {
            FileName:string;
        }
        with interface IEnvironmentVariable

    [<RequireQualifiedAccess>]
    type NusmvStdout = {
            FileName:string;
        }
        with interface IEnvironmentVariable

    [<RequireQualifiedAccess>]
    type NusmvStdIn = {
            FileName:string;
        }
        with interface IEnvironmentVariable

[<RequireQualifiedAccess>]
type internal NuXmvCommand =
    // Chapter 5.1 Model Simulation
    | MsatPickState
    | MsatSimulate
    // Chapter 5.2 Invariant Checking
    | MsatCheckInvarBmc
    | CheckInvarBmcItp
    | CheckInvarIc3
    // ... many more to evaluate
    // Chapter 5.3 LTL Model Checking
    | MsatCheckLtlspecBmc
    | CheckLtlspecKlive
    | CheckLtlspecSimplify
    | CheckLtlspecCompositional
    // ... many more to evaluate
    // Chapter 5.4 Computing Reachable States
    // Chapter 5.5 Reasoning via Abstraction
    // Chapter 5.6 Format Conversions
    // Chapter 5.7 Model Transformation
    | WriteSimplifiedModelRel //<----- Check this out
    | WriteSimplifiedModelFunc  //<----- Check this out. I don't get the difference between both simplifiers
    | BuildSimplifiedProperty
    with interface ICommand

// Chapter 5.8 Environment Variables
module internal NuXmvEnvironmentVariables = 
    // Cone Of Influence
    
    [<RequireQualifiedAccess>]
    type AbstractionEngine =
        | Msat
        | Structural
        | Hybrid
        | Bdd
        with interface IEnvironmentVariable
        
[<RequireQualifiedAccess>]
type internal NuXmvCommandLine =
    | Help
    | Verbose
    | Interactive
    | AvoidLoadingDefaultSettings // -s

module internal NuXmvHelpfulCommandSequences =
    let readmodel (filename: string ) = [
        NuSMVCommand.ReadModel filename
    ]
    let switchToXmlOutput = [
    ]
    let goCommandExpanded (filename:string) = [
        NuSMVCommand.ReadModel filename;
        NuSMVCommand.FlattenHierarchy;
        NuSMVCommand.EncodeVariables;
        NuSMVCommand.BuildFlatModel;
        NuSMVCommand.BuildModel;
    ]