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
module AtDccaLtlTests =
    let internal inputFileToScmWorkflow (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
            let! scmModel = getState ()
            return scmModel
    }

    let internal faultNo1 = [Scm.Comp("simple")], Scm.Fault("faultNo1")
    let internal faultNo2 = [Scm.Comp("simple")], Scm.Fault("faultNo2")
    let internal faultNo3 = [Scm.Comp("simple")], Scm.Fault("faultNo3")
    let internal faultNo4 = [Scm.Comp("simple")], Scm.Fault("faultNo4")
        
    [<Test>]
    let ``check ElementToCheck generator on dcca1`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let scmExample = runWorkflow_getResult (inputFileToScmWorkflow inputFile)
        let hazard = ScmVerificationElements.PropositionalExpr.Literal(Scm.BoolVal(false))
        
        let analyzer = AtDccaLtl.PerformDccaWithLtlFormulas (scmExample.Model,hazard)
        
        let elementToCheck1 = analyzer.``even when these faults appear, system is safe`` ([faultNo1;faultNo4] |> Set.ofList)
        let elementToCheck2 = analyzer.``even when these faults appear, system is safe`` ([] |> Set.ofList)
        let elementToCheck3 = analyzer.``even when these faults appear, system is safe`` ([faultNo1;faultNo2;faultNo3;faultNo4] |> Set.ofList)
        elementToCheck1 =?
            {
                FaultsWhichMayAppear = ([([Scm.Comp "simple"], Scm.Fault "faultNo1"); ([Scm.Comp "simple"], Scm.Fault "faultNo4")] |> Set.ofList);
                FaultsWhichMustNotAppear = ([([Scm.Comp "simple"], Scm.Fault "faultNo2"); ([Scm.Comp "simple"], Scm.Fault "faultNo3")] |> Set.ofList);
                CorrespondingFormula = LtlExpr.UExpr(LtlExpr.LbExpr(LtlExpr.BExpr(LtlExpr.UExpr (LtlExpr.ReadFault ([Scm.Comp "simple"],Scm.Fault "faultNo2"),Scm.Not),Scm.And,LtlExpr.UExpr (LtlExpr.ReadFault ([Scm.Comp "simple"],Scm.Fault "faultNo3"),Scm.Not)),LbOp.Until,LtlExpr.Literal (Scm.BoolVal false)),Scm.Not);
            }

        elementToCheck2 =?
            {
                FaultsWhichMayAppear = set [];
                FaultsWhichMustNotAppear =set[([Scm.Comp "simple"], Scm.Fault "faultNo1"); ([Scm.Comp "simple"], Scm.Fault "faultNo2");([Scm.Comp "simple"], Scm.Fault "faultNo3"); ([Scm.Comp "simple"], Scm.Fault "faultNo4")];
                CorrespondingFormula = LtlExpr.UExpr(LtlExpr.LbExpr(LtlExpr.BExpr(LtlExpr.UExpr (LtlExpr.ReadFault ([Scm.Comp "simple"],Scm.Fault "faultNo1"),Scm.Not),Scm.And,LtlExpr.BExpr(LtlExpr.UExpr (LtlExpr.ReadFault ([Scm.Comp "simple"],Scm.Fault "faultNo2"),Scm.Not),Scm.And,LtlExpr.BExpr(LtlExpr.UExpr (LtlExpr.ReadFault ([Scm.Comp "simple"],Scm.Fault "faultNo3"),Scm.Not),Scm.And,LtlExpr.UExpr (LtlExpr.ReadFault ([Scm.Comp "simple"],Scm.Fault "faultNo4"),Scm.Not)))),LbOp.Until,LtlExpr.Literal (Scm.BoolVal false)),Scm.Not);
            }
        elementToCheck3 =?
            {
                FaultsWhichMayAppear = set[([Scm.Comp "simple"], Scm.Fault "faultNo1"); ([Scm.Comp "simple"], Scm.Fault "faultNo2");([Scm.Comp "simple"], Scm.Fault "faultNo3"); ([Scm.Comp "simple"], Scm.Fault "faultNo4")];
                FaultsWhichMustNotAppear = set [];
                CorrespondingFormula = LtlExpr.UExpr (LtlExpr.LbExpr (LtlExpr.Literal (Scm.BoolVal true),LbOp.Until,LtlExpr.Literal (Scm.BoolVal false)),Scm.Not);
            }

    [<Test>]
    let ``check isAlreadyKnownThatUnsafe on dcca1`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let scmExample = runWorkflow_getResult (inputFileToScmWorkflow inputFile)
        let hazard = ScmVerificationElements.PropositionalExpr.Literal(Scm.BoolVal(false))
        
        let analyzer = AtDccaLtl.PerformDccaWithLtlFormulas (scmExample.Model,hazard)
        
        let known = [([faultNo1;faultNo4] |> Set.ofList)] |> Set.ofList
        
        (analyzer.isAlreadyKnownThatUnsafe known ([faultNo1;faultNo2;faultNo4] |> Set.ofList)) =? true
        (analyzer.isAlreadyKnownThatUnsafe known ([faultNo1;faultNo2;faultNo4;faultNo4] |> Set.ofList)) =? true
        (analyzer.isAlreadyKnownThatUnsafe known ([faultNo2;faultNo4;faultNo4] |> Set.ofList)) =? false


    [<Test>]
    let ``check formulasToVerify_CheckIfNumberOfFaultsIsSafe on dcca1`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let scmExample = runWorkflow_getResult (inputFileToScmWorkflow inputFile)
        let hazard = ScmVerificationElements.PropositionalExpr.Literal(Scm.BoolVal(false))
        
        let analyzer = AtDccaLtl.PerformDccaWithLtlFormulas (scmExample.Model,hazard)
        
        let elementOfSize2 = ([faultNo1;faultNo4] |> Set.ofList)

        let formulas0 = analyzer.formulasToVerify_CheckIfNumberOfFaultsIsSafe 0 (Set.empty)
        let formulas1_if_formal_verification_successful = analyzer.formulasToVerify_CheckIfNumberOfFaultsIsSafe 1 (Set.empty)
        let formulas2_if_no_single_point_of_failure = analyzer.formulasToVerify_CheckIfNumberOfFaultsIsSafe 2 (Set.empty)
        let formulas3_if_one_element_of_size_2_failed = analyzer.formulasToVerify_CheckIfNumberOfFaultsIsSafe 3 ([elementOfSize2]|>Set.ofList)
        let formulas4_if_formal_verification_failed = analyzer.formulasToVerify_CheckIfNumberOfFaultsIsSafe 4 (Set.empty.Add(Set.empty))
        formulas0.Length =? 1
        formulas1_if_formal_verification_successful.Length =? 4
        formulas2_if_no_single_point_of_failure.Length =? 6
        formulas3_if_one_element_of_size_2_failed.Length =? 2
        formulas4_if_formal_verification_failed.Length =? 0

    
    [<Test>]
    let ``perform DCCA on callInstHierarchyWithFaults1 with Spin`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaults1.scm"""
        let hazardAsString = "false"
        
        let analyzer = new AnalysisFacade ()
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaLtl_WithPromela (hazardAsString)
        dccaResult.Count =? 0
    
    [<Test>]
    let ``perform DCCA on dcca1 with Spin`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let hazardAsString = "simple.isHazard == true"
        
        let analyzer = new AnalysisFacade ()
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaLtl_WithPromela (hazardAsString)
        dccaResult.Count =? 3
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true
    
    [<Test>]
    let ``perform DCCA on dcca1 with NuSMV`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let hazardAsString = "simple.isHazard == true"

        let analyzer = new AnalysisFacade ()
        do analyzer.setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)
        do analyzer.setMainModelFromFile (inputFile)
        let dccaResult = analyzer.atAnalyseDccaLtl_WithNuSmv (hazardAsString)
        dccaResult.Count =? 3
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> Set.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true