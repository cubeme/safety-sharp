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

namespace SafetySharp.Tests.Models.Scm.RewriterTests

open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers
open SafetySharp.Internal
open SafetySharp.Models.Scm
open ScmHelpers
open ScmRewriterBase

[<TestFixture>]
type CompleteRewriteTests () =

    let runWithUserState parser str = runParserOnString parser Parser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (Parser.scmFile .>> eof) str
    
    [<Test>]
    member this.``Example nestedComponent3 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh2 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh3 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh4 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()
        
    [<Test>]
    member this.``Example callInstFromBeh5 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh6 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh7 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromBeh8 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBeh8.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

        

    [<Test>]
    member this.``Example callInstFromProv1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromProv1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()



    [<Test>]
    member this.``Example callInstHierarchy1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy2 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy3 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy4 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy5 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy6 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callDelayedSimple1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimple1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()


        
    [<Test>]
    member this.``Example nestedComponentWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults2 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example simpleComponentWithFaults3 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/simpleComponentWithFaults3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example behWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/behWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()
        
    [<Test>]
    member this.``Example callInstFromBehWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromBehWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstFromProvWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstFromProvWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchyWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchyWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callDelayedSimpleWithFaults1 gets rewritten (leveled up and inlined) completely`` () =
        let inputFile = """../../Examples/SCM/callDelayedSimpleWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        //model.ProvPorts.Length =? 0
        let initialState = ScmRewriteState.initial model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()