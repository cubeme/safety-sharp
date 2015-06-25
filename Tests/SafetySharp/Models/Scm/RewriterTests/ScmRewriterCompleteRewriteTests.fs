﻿// The MIT License (MIT)
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
open SafetySharp.Workflow
open SafetySharp.Models
open SafetySharp.Models.Scm
open SafetySharp.Models.ScmHelpers
open SafetySharp.Models.ScmRewriterBase


[<TestFixture>]
type CompleteRewriteTests () =
    
    let rewriteWorkflow (inputFile:string)= 
        workflow {
            do! readFile inputFile
            do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
            do! ScmRewriterFlattenModel.flattenModel ()  
            do! ScmTracer.iscmCommitForwardTracerMap ()
            let! model = getState ()
            do printf "%s" (SafetySharp.Models.ScmToString.toString model.Model.getRootComp)
            do! SafetySharp.Workflow.printNewParagraphToStdout ()
            do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
            do! SafetySharp.Workflow.printNewParagraphToStdout ()
            do! SafetySharp.Workflow.printObjectToStdout () 
            let! allTraceablesExist = ScmConsistencyCheck.``check if all traced traceables from origin actually exists`` ()
            allTraceablesExist =? true
        }
    
    [<Test>]
    member this.``Example beh3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/beh3.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)
        
    [<Test>]
    member this.``Example nestedComponent3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh2.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh3.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh4 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh4.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)
        
    [<Test>]
    member this.``Example callInstFromBeh5 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh5.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh6 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh6.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh7 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh7.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromBeh8 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh8.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

        

    [<Test>]
    member this.``Example callInstFromProv1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromProv1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)



    [<Test>]
    member this.``Example callInstHierarchy1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstHierarchy2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy2.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstHierarchy3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy3.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstHierarchy4 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy4.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstHierarchy5 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstHierarchy6 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy6.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callDelayedSimple1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimple1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)


        
    [<Test>]
    member this.``Example nestedComponentWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponentWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example simpleComponentWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example simpleComponentWithFaults2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults2.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example simpleComponentWithFaults3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults3.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example behWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/behWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)
        
    [<Test>]
    member this.``Example callInstFromBehWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBehWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstFromProvWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromProvWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callInstHierarchyWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example callDelayedSimpleWithFaults1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimpleWithFaults1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example exampleBackupRecovery1 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery1.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example exampleBackupRecovery2 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery2.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)

    [<Test>]
    member this.``Example exampleBackupRecovery3 gets flattened completely`` () =
        let inputFile = """../../Examples/SCM/exampleBackupRecovery3.scm"""
        do SafetySharp.Workflow.runWorkflow_getResult (rewriteWorkflow inputFile)