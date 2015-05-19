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

namespace SafetySharp.Modelchecking

open NUnit.Framework

open SafetySharp.Models
open SafetySharp.Workflow
open SafetySharp.Analysis.Techniques

[<TestFixture>]
module AtDccaLtlTests =
    let internal inputFileToScmWorkflow (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
            let! scmModel = getState ()
            return scmModel
    }
        
    [<Test>]
    let ``check ElementToCheck generator on dcca1`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let scmExample = runWorkflow_getResult (inputFileToScmWorkflow inputFile)
        let hazard = ScmVerificationElements.PropositionalExpr.Literal(Scm.BoolVal(false))
        
        let analyzer = AtDccaLtl.PerformDccaWithLtlFormulas (scmExample.Model,hazard)

        //let dccaResult = analyzer.checkWithPromela ()
        ()
    
    [<Test>]
    let ``perform DCCA on callInstHierarchyWithFaults1`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaults1.scm"""
        let scmExample = runWorkflow_getResult (inputFileToScmWorkflow inputFile)
        let hazard = ScmVerificationElements.PropositionalExpr.Literal(Scm.BoolVal(false))
        
        let analyzer = AtDccaLtl.PerformDccaWithLtlFormulas (scmExample.Model,hazard)

        let dccaResult = analyzer.checkWithPromela ()
        ()
    
    [<Test>]
    let ``perform DCCA on dcca1`` () =
        let inputFile = """../../Examples/SCM/dcca1.scm"""
        let scmExample = runWorkflow_getResult (inputFileToScmWorkflow inputFile)
        let hazard = 
            let readField = ScmVerificationElements.PropositionalExpr.ReadField( ( [Scm.Comp("simple")], Scm.Field("isHazard") ) )
            let trueValue = ScmVerificationElements.PropositionalExpr.Literal(Scm.Val.BoolVal(true))
            ScmVerificationElements.PropositionalExpr.BExpr(readField,Scm.BOp.Equals,trueValue)
        
        let analyzer = AtDccaLtl.PerformDccaWithLtlFormulas (scmExample.Model,hazard)
        
        let faultNo1 = [Scm.Comp("simple")], Scm.Fault("faultNo1")
        let faultNo2 = [Scm.Comp("simple")], Scm.Fault("faultNo2")
        let faultNo3 = [Scm.Comp("simple")], Scm.Fault("faultNo3")
        let faultNo4 = [Scm.Comp("simple")], Scm.Fault("faultNo4")

        let dccaResult = analyzer.checkWithPromela ()
        dccaResult.Length =? 3
        (dccaResult |> List.exists (fun gamma -> gamma = ([faultNo1;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> List.exists (fun gamma -> gamma = ([faultNo2;faultNo3;faultNo4] |> Set.ofList))) =? true
        (dccaResult |> List.exists (fun gamma -> gamma = ([faultNo1;faultNo2] |> Set.ofList))) =? true