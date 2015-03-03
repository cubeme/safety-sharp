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

namespace Models.Scm

open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers
open SafetySharp.Models
open SafetySharp.Models.Scm
open SafetySharp.Models.ScmHelpers
open SafetySharp.Models.ScmRewriterBase
open SafetySharp.Models.ScmWorkflow

[<TestFixture>]
type CompleteRewriteTests () =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str
    
    [<Test>]
    member this.``Example beh5 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/beh5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()
        
    [<Test>]
    member this.``Example nestedComponent3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh4 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()
        
    [<Test>]
    member this.``Example callInstFromBeh5 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh6 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh7 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh8 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh8.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

        

    [<Test>]
    member this.``Example callInstFromProv1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromProv1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()



    [<Test>]
    member this.``Example callInstHierarchy1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy4 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy5 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy6 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callDelayedSimple1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimple1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()


        
    [<Test>]
    member this.``Example nestedComponentWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example behWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/behWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example behWithFaults2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/behWithFaults2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()
        
    [<Test>]
    member this.``Example callInstFromBehWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBehWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromProvWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromProvWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchyWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callDelayedSimpleWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimpleWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = ScmRewriterFlattenModel.flattenModel
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.getModel
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()