﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineeringgineering
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

namespace SafetySharp.Modelchecking.NuXmv.NuXmvTransformMetamodelTests


open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers

open SafetySharp.Workflow
open SafetySharp.Analysis.Modelchecking.NuXmv

[<TestFixture>]
module ScmToNuXmvTests =
    
    
    let internal inputFileToNuXmvAstWorkflow (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.ScmParser.parseStringWorkflow ()
            do! SafetySharp.Models.ScmToSam.transformIscmToSam
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
            do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModelFast.transformWorkflow ()
            do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformGwamToTsareWorkflow ()
            do! SafetySharp.Analysis.Modelchecking.NuXmv.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
            do! SafetySharp.ITracing.removeTracing ()
            do! SafetySharp.Analysis.Modelchecking.NuXmv.NuXmvToString.workflow ()
        }
           
    [<Test>]
    let ``nestedComponent3.scm gets converted to NuXmv`` () =

        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let output = runWorkflow_getState (inputFileToNuXmvAstWorkflow inputFile)
        printf "%s" output
        ()
        
    [<Test>]
    let ``callInstHierarchy1.scm gets converted to NuXmv`` () =

        let inputFile = """../../Examples/SCM/callInstHierarchy1.scm"""
        let output = runWorkflow_getState (inputFileToNuXmvAstWorkflow inputFile)
        printf "%s" output
        ()
        
    [<Test>]
    let ``callInstFromBeh2.scm gets converted to NuXmv`` () =

        let inputFile = """../../Examples/SCM/callInstFromBeh2.scm"""
        let output = runWorkflow_getState (inputFileToNuXmvAstWorkflow inputFile)
        printf "%s" output
           
        
    [<Test>]
    let ``simpleComponentWithFaults3.scm gets converted to NuXmv`` () =

        let inputFile = """../../Examples/SCM/simpleComponentWithFaults3.scm"""
        let output = runWorkflow_getState (inputFileToNuXmvAstWorkflow inputFile)
        printf "%s" output
           

