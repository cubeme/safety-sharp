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

namespace SafetySharp.EngineOptions

type IEngineOption =
    interface
        inherit System.IComparable
    end

module internal EngineOptionHelpers =
    let addStandardToList<'engineOption when 'engineOption :> IEngineOption>
                (toAdd:'engineOption)
                (currentStandards:(string*IEngineOption) list)
            : (string*IEngineOption) list =
        let nameOfEngineOptionAsString =
            let typeOfEngineOption = typeof<'engineOption>
            typeOfEngineOption.AssemblyQualifiedName
        let newElement = (nameOfEngineOptionAsString,toAdd :> IEngineOption)
        newElement :: currentStandards

    let nameOfEngineOptionAsString<'engineOption when 'engineOption :> IEngineOption> () =
        let typeOfEngineOption = typeof<'engineOption>
        typeOfEngineOption.AssemblyQualifiedName

module internal TsamEngineOptions =

    [<RequireQualifiedAccessAttribute>]
    type SemanticsOfAssignmentToRangedVariables =
        | ForceRangesAfterStep
        | ForceRangeAfterEveryAssignmentToAGlobalVar
        | ForceRangeAfterFinalAssignmentToAGlobalVar //not used anywhere. Just for theoretical purposes
        | IgnoreRanges //Useful for Simulations
        // Example, where it makes a difference:
        //  Assume x in 2..4,
        //       y,z in 0..10:
        //     x:= 10;
        //     if x >= 5 {y=x;};
        //     x:= 5;
        //     if x >= 5 {z=x;};
        //  ForceRangesAfterStep: x=4, y=10, z=5
        //  ForceRangeAfterEveryAssignmentToAGlobalVar: x=4, y=4, z=4
        //  ForceRangeAfterFinalAssignmentToAGlobalVar: x=4, y=5, z=4
        //  IgnoreRanges: x=5, y=10, z=5
        with
            interface IEngineOption
            member this.isForceRangeAfterEveryAssignmentToAGlobalVar =
                match this with
                    | ForceRangeAfterEveryAssignmentToAGlobalVar -> true
                    | _ -> false

    let standardValues : (string*IEngineOption) list =
            [] |> EngineOptionHelpers.addStandardToList (SemanticsOfAssignmentToRangedVariables.IgnoreRanges)

            
module internal AtEngineOptions =

    [<RequireQualifiedAccessAttribute>]
    type StandardVerifier =
        | NuSMV
        | Promela
        with
            interface IEngineOption

    let standardValues : (string*IEngineOption) list =
            [] |> EngineOptionHelpers.addStandardToList (StandardVerifier.Promela)


module DefaultEngineOptions = 

    let private DefaultEngineOptionsLazy =
        lazy (
            let elements =
                TsamEngineOptions.standardValues @
                AtEngineOptions.standardValues
            elements |> Map.ofList
        )

    let DefaultEngineOptions = DefaultEngineOptionsLazy.Force ()
    
        
