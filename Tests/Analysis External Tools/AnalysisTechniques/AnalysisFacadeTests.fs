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

namespace SafetySharp.AnalysisTechniques

open NUnit.Framework

open SafetySharp.Models
open SafetySharp.Workflow
open SafetySharp.AnalysisTechniques
open SafetySharp.Models.ScmVerificationElements
open SafetySharp.EngineOptions

[<TestFixture>]
module AnalysisFacadeTests =


    [<Test>]
    let ``check exampleBackupRecovery1.scm with atAnalyseLtl (Verifier: Promela)`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery1.scm"""                       
        let formula = "[] (backupRecoverySystem.in.sourceValueField == backupRecoverySystem.out.result)"
                
        let analyzer = new AnalysisFacade ()
        do analyzer.setEngineOption (SafetySharp.EngineOptions.AtEngineOptions.StandardVerifier.Promela)
        do analyzer.setMainModelFromFile (inputFile)
        let result1 = analyzer.atAnalyseLtl (formula)

        ()
    
    let faultNo1 = "simple.faultNo1"
    let faultNo2 = "simple.faultNo2"
    let faultNo3 = "simple.faultNo3"
    let faultNo4 = "simple.faultNo4"
    
    [<Test>]
    let ``check dcca1.scm with atAnalyseDccaLtl (Verifier: Promela)`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let hazardAsString = "simple.isHazard == true"
        
        let analyzer = new AnalysisFacade ()
        do analyzer.setEngineOption (SafetySharp.EngineOptions.AtEngineOptions.StandardVerifier.Promela)
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaLtl (hazardAsString)
        dccaResult.Count =? 3
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true
    
    [<Test>]
    let ``check dcca1.scm with atAnalyseDccaLtl (Verifier: NuSMV)`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let hazardAsString = "simple.isHazard == true"

        let analyzer = new AnalysisFacade ()
        do analyzer.setEngineOption (SafetySharp.EngineOptions.AtEngineOptions.StandardVerifier.NuSMV)
        do analyzer.setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaLtl (hazardAsString)
        dccaResult.Count =? 3
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true

    [<Test>]
    let ``check dcca1.scm with atAnalyseDccaPruning (Verifier: Promela)`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let hazardAsString = "simple.isHazard == true"
        
        let analyzer = new AnalysisFacade ()
        do analyzer.setEngineOption (SafetySharp.EngineOptions.AtEngineOptions.StandardVerifier.Promela)
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaPruning (hazardAsString)
        dccaResult.Count =? 3
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true
    
    [<Test>]
    let ``check dcca1.scm with atAnalyseDccaPruning (Verifier: NuSMV)`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let hazardAsString = "simple.isHazard == true"

        let analyzer = new AnalysisFacade ()
        do analyzer.setEngineOption (SafetySharp.EngineOptions.AtEngineOptions.StandardVerifier.NuSMV)
        do analyzer.setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaPruning (hazardAsString)
        dccaResult.Count =? 3
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true