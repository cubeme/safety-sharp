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
open SafetySharp.Workflow
open SafetySharp.Models
open SafetySharp.Models.ScmHelpers
open SafetySharp.Models.Scm

open SafetySharp.Models.ScmRewriterBase
open SafetySharp.Models.ScmRewriterLevelUp
open SafetySharp.Models.ScmRewriterConvertFaults
open SafetySharp.Models.ScmRewriterInlineBehavior
open SafetySharp.Models.ScmRewriterFlattenModel

[<TestFixture>]
type SingleLevelUpTests () =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str
            
    [<Test>]
    member this.``A simple field in a nested component gets leveled up`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested_n22") :: Comp("nested_n2") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.Fields.Length =? 1
        parentNode.Fields.Length =? 1
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpField
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.Fields.Length =? 0
        newParentNode.Fields.Length =? 2        
        ()
        
    [<Test>]
    member this.``A simple field in a sub component gets leveled up`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested_n2") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.Fields.Length =? 1
        parentNode.Fields.Length =? 1
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpField
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.Fields.Length =? 0
        newParentNode.Fields.Length =? 2        
        ()

    [<Test>]
    member this.``A simple fault in a sub component gets leveled up`` () =
        let inputFile = """../../Examples/SCM/nestedComponentWithFaults1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.Faults.Length =? 2
        parentNode.Faults.Length =? 0
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpFault
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.Faults.Length =? 1
        newParentNode.Faults.Length =? 1
        ()

    [<Test>]
    member this.``A required Port in a sub component gets leveled up`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nestedRequired") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 1
        parentNode.ReqPorts.Length =? 0
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newParentNode.ReqPorts.Length =? 1     
        ()


    [<Test>]
    member this.``A provided Port in a sub component gets leveled up`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nestedProvided") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ProvPorts.Length =? 1
        parentNode.ProvPorts.Length =? 0
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpProvPort
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ProvPorts.Length =? 0
        newParentNode.ProvPorts.Length =? 1     
        ()
        
    [<Test>]
    member this.``A binding in a sub component gets leveled up and rewritten`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works

        let inputFile = """../../Examples/SCM/callInstHierarchy6.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 1
        childNode.Bindings.Length =? 1
        childNode.Bindings.Head.Source.Comp =? [Comp("nested")]
        childNode.Bindings.Head.Target.Comp =? [Comp("nested")]
        parentNode.ReqPorts.Length =? 0
        parentNode.ProvPorts.Length =? 0
        parentNode.Bindings.Length =? 0
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.levelUpProvPort
            do! ScmRewriterLevelUp.levelUpAndRewriteBindingDeclaredInChild
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newParentNode.ReqPorts.Length =? 1
        newParentNode.ProvPorts.Length =? 1
        newParentNode.Bindings.Length =? 1   
        newParentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        newParentNode.Bindings.Head.Target.Comp =? [Comp("simple")]  
        ()
        
    [<Test>]
    member this.``A binding in a parent component gets rewritten (source=parent;target=child)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 0
        childNode.Bindings.Length =? 0
        parentNode.ReqPorts.Length =? 0
        parentNode.ProvPorts.Length =? 1
        parentNode.Bindings.Length =? 1
        parentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        parentNode.Bindings.Head.Target.Comp =? [Comp("nested"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newParentNode.ReqPorts.Length =? 1
        newParentNode.ProvPorts.Length =? 1
        newParentNode.Bindings.Length =? 1
        newParentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        newParentNode.Bindings.Head.Target.Comp =? [Comp("simple")]
        ()

    [<Test>]
    member this.``A binding in a parent component gets rewritten (source=child;target=parent)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 0
        childNode.ProvPorts.Length =? 1
        childNode.Bindings.Length =? 0
        parentNode.ReqPorts.Length =? 1
        parentNode.ProvPorts.Length =? 0
        parentNode.Bindings.Length =? 1
        parentNode.Bindings.Head.Source.Comp =? [Comp("nested"); Comp("simple")]
        parentNode.Bindings.Head.Target.Comp =? [Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpProvPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newParentNode.ReqPorts.Length =? 1
        newParentNode.ProvPorts.Length =? 1
        newParentNode.Bindings.Length =? 1
        newParentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        newParentNode.Bindings.Head.Target.Comp =? [Comp("simple")]
        ()
        
    [<Test>]
    member this.``A binding in a parent component gets rewritten (source=child;target=child)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 1
        childNode.Bindings.Length =? 0
        parentNode.ReqPorts.Length =? 0
        parentNode.ProvPorts.Length =? 0
        parentNode.Bindings.Length =? 1
        parentNode.Bindings.Head.Source.Comp =? [Comp("nested"); Comp("simple")]
        parentNode.Bindings.Head.Target.Comp =? [Comp("nested"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.levelUpProvPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newParentNode.ReqPorts.Length =? 1
        newParentNode.ProvPorts.Length =? 1
        newParentNode.Bindings.Length =? 1
        newParentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        newParentNode.Bindings.Head.Target.Comp =? [Comp("simple")]
        ()
        
    [<Test>]
    member this.``A binding in a parent component gets rewritten (source=child;target=different child)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nestedProvided") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 0
        childNode.ProvPorts.Length =? 1
        childNode.Bindings.Length =? 0
        parentNode.ReqPorts.Length =? 0
        parentNode.ProvPorts.Length =? 0
        parentNode.Bindings.Length =? 1
        parentNode.Bindings.Head.Source.Comp =? [Comp("nestedProvided"); Comp("simple")]
        parentNode.Bindings.Head.Target.Comp =? [Comp("nestedRequired"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpProvPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newParentNode.ReqPorts.Length =? 0
        newParentNode.ProvPorts.Length =? 1
        newParentNode.Bindings.Length =? 1
        newParentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        newParentNode.Bindings.Head.Target.Comp =? [Comp("nestedRequired"); Comp("simple")]
        ()

    [<Test>]
    member this.``A binding in a parent component gets rewritten (source=different child;target=child)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nestedRequired") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 0
        childNode.Bindings.Length =? 0
        parentNode.ReqPorts.Length =? 0
        parentNode.ProvPorts.Length =? 0
        parentNode.Bindings.Length =? 1
        parentNode.Bindings.Head.Source.Comp =? [Comp("nestedProvided"); Comp("simple")]
        parentNode.Bindings.Head.Target.Comp =? [Comp("nestedRequired"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newParentNode.ReqPorts.Length =? 1
        newParentNode.ProvPorts.Length =? 0
        newParentNode.Bindings.Length =? 1
        newParentNode.Bindings.Head.Source.Comp =? [Comp("nestedProvided"); Comp("simple")]
        newParentNode.Bindings.Head.Target.Comp =? [Comp("simple")]
        ()
        
    [<Test>]
    member this.``A binding in a grandparent component gets rewritten (source=different grandchild;target=grandchild)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested2Required") :: Comp("nestedRequired") :: Comp("simple") :: []
        let pathOfGrandparent = pathOfChild.Tail.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let grandparentNode = model.getDescendantUsingPath pathOfGrandparent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 0
        childNode.Bindings.Length =? 0
        grandparentNode.ReqPorts.Length =? 0
        grandparentNode.ProvPorts.Length =? 0
        grandparentNode.Bindings.Length =? 1
        grandparentNode.Bindings.Head.Source.Comp =? [Comp("nested2Provided"); Comp("nestedProvided"); Comp("simple")]
        grandparentNode.Bindings.Head.Target.Comp =? [Comp("nested2Required"); Comp("nestedRequired"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newGrandparentNode = newModel.getDescendantUsingPath pathOfGrandparent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newGrandparentNode.ReqPorts.Length =? 0
        newGrandparentNode.ProvPorts.Length =? 0
        newGrandparentNode.Bindings.Length =? 1
        newGrandparentNode.Bindings.Head.Source.Comp =? [Comp("nested2Provided"); Comp("nestedProvided"); Comp("simple")]
        newGrandparentNode.Bindings.Head.Target.Comp =? [Comp("nestedRequired"); Comp("simple")]
        ()
        
    [<Test>]
    member this.``A binding in a grandparent component gets rewritten (source=grandchild;target=different grandchild)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested2Provided") :: Comp("nestedProvided") :: Comp("simple") :: []
        let pathOfGrandparent = pathOfChild.Tail.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let grandparentNode = model.getDescendantUsingPath pathOfGrandparent
        childNode.ReqPorts.Length =? 0
        childNode.ProvPorts.Length =? 1
        childNode.Bindings.Length =? 0
        grandparentNode.ReqPorts.Length =? 0
        grandparentNode.ProvPorts.Length =? 0
        grandparentNode.Bindings.Length =? 1
        grandparentNode.Bindings.Head.Source.Comp =? [Comp("nested2Provided"); Comp("nestedProvided"); Comp("simple")]
        grandparentNode.Bindings.Head.Target.Comp =? [Comp("nested2Required"); Comp("nestedRequired"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpProvPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newGrandparentNode = newModel.getDescendantUsingPath pathOfGrandparent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newGrandparentNode.ReqPorts.Length =? 0
        newGrandparentNode.ProvPorts.Length =? 0
        newGrandparentNode.Bindings.Length =? 1
        newGrandparentNode.Bindings.Head.Source.Comp =? [Comp("nestedProvided"); Comp("simple")]
        newGrandparentNode.Bindings.Head.Target.Comp =? [Comp("nested2Required"); Comp("nestedRequired"); Comp("simple")]
        ()
        
    [<Test>]
    member this.``A binding in a great-grandparent component gets rewritten (source=root;target=great-grandchild)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy8.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested3Required") :: Comp("nested2Required") :: Comp("nestedRequired") :: Comp("simple") :: []
        let pathOfGrandparent = pathOfChild.Tail.Tail.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let greatgrandparentNode = model.getDescendantUsingPath pathOfGrandparent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 0
        childNode.Bindings.Length =? 0
        greatgrandparentNode.ReqPorts.Length =? 0
        greatgrandparentNode.ProvPorts.Length =? 1
        greatgrandparentNode.Bindings.Length =? 1
        greatgrandparentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        greatgrandparentNode.Bindings.Head.Target.Comp =? [Comp("nested3Required"); Comp("nested2Required"); Comp("nestedRequired"); Comp("simple")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newGreatgrandparentNode = newModel.getDescendantUsingPath pathOfGrandparent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newGreatgrandparentNode.ReqPorts.Length =? 0
        newGreatgrandparentNode.ProvPorts.Length =? 1
        newGreatgrandparentNode.Bindings.Length =? 1
        newGreatgrandparentNode.Bindings.Head.Source.Comp =? [Comp("simple")]
        newGreatgrandparentNode.Bindings.Head.Target.Comp =? [Comp("nested2Required"); Comp("nestedRequired"); Comp("simple")]
        ()

        
    [<Test>]
    member this.``A binding in a grandparent component gets rewritten (source=non-root;target=grandchild)`` () =
        // this function needs the map entries of provided and required ports
        // either fake it, or assume, that levelUpReqPort and levelUpProvPort works
        let inputFile = """../../Examples/SCM/callInstHierarchy9.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested3Required") :: Comp("nested2Required") :: Comp("nested") :: Comp("simple") :: []
        let pathOfGrandparent = pathOfChild.Tail.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let grandparentNode = model.getDescendantUsingPath pathOfGrandparent
        childNode.ReqPorts.Length =? 1
        childNode.ProvPorts.Length =? 0
        childNode.Bindings.Length =? 0
        grandparentNode.ReqPorts.Length =? 0
        grandparentNode.ProvPorts.Length =? 1
        grandparentNode.Bindings.Length =? 1
        grandparentNode.Bindings.Head.Source.Comp =? [Comp("nested")]
        grandparentNode.Bindings.Head.Target.Comp =? [Comp("nested3Required"); Comp("nested2Required"); Comp("nested")]
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! ScmRewriterLevelUp.levelUpReqPort
            do! ScmRewriterLevelUp.rewriteBindingsDeclaredInAncestors
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newGrandparentNode = newModel.getDescendantUsingPath pathOfGrandparent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.ReqPorts.Length =? 0
        newChildNode.ProvPorts.Length =? 0
        newChildNode.Bindings.Length =? 0
        newGrandparentNode.ReqPorts.Length =? 0
        newGrandparentNode.ProvPorts.Length =? 1
        newGrandparentNode.Bindings.Length =? 1
        newGrandparentNode.Bindings.Head.Source.Comp =? [Comp("nested")]
        newGrandparentNode.Bindings.Head.Target.Comp =? [Comp("nested2Required"); Comp("nested")]
        ()



[<TestFixture>]
type FixpointIteratorTests () =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str

    [<Test>]
    member this.``Several fields get leveled up by using levelUpFields with the iterateToFixpoint function`` () =
        let inputFile = """../../Examples/SCM/nestedComponent4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathOfChild = Comp("nested") :: Comp("simple") :: []
        let pathOfParent = pathOfChild.Tail
        let childNode = model.getDescendantUsingPath pathOfChild
        let parentNode = model.getDescendantUsingPath pathOfParent
        childNode.Fields.Length =? 3
        parentNode.Fields.Length =? 1
        let initialState = (ScmRewriterLevelUp.initialLevelUpWorkflowState model pathOfChild) 
        let workFlow = workflow {
            do! (iterateToFixpoint ScmRewriterLevelUp.levelUpField) 
            return ()
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.Fields.Length =? 0
        newParentNode.Fields.Length =? 4
        ()
        
[<TestFixture>]
type CompleteLevelUpTests () =

    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str
    
    [<Test>]
    member this.``Example nestedComponent1 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent1.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        // 1 Artificial Prov Port, which contains the code of the previous nested step
        newModel.ProvPorts.Length =? 1
        ()
        
    [<Test>]
    member this.``Example nestedComponent2 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        // 4 Artificial Prov Ports, which contain the code of the previous nested steps
        newModel.ProvPorts.Length =? 4
        ()

    [<Test>]
    member this.``Example nestedComponent3 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent3.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example nestedComponent4 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent4.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example nestedComponent5 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/nestedComponent5.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy2 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()

    [<Test>]
    member this.``Example callInstHierarchy7 gets leveled up completely`` () =
        let inputFile = """../../Examples/SCM/callInstHierarchy7.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        model.ProvPorts.Length =? 0
        let initialState = createPlainScmWorkFlowState model
        let workFlow = workflow {
            do! levelUpSubcomponentsWrapper
        }
        let resultingState = SafetySharp.Workflow.runWorkflowState_getState workFlow initialState
        let newModel = resultingState.State.Model
        printf "%s" (SafetySharp.Models.ScmToString.toString newModel)
        printfn ""
        printfn ""
        printf "%+A" newModel
        resultingState.Tainted =? true
        newModel.Subs =? []
        ()
(*       
        
[<TestFixture>]
type InliningTests () =

    let runWithUserState parser str = runParserOnString parser Parser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (Parser.scmFile .>> eof) str
    
*)
    
// TODO: Write test, which ensures, that if a child component
//       contains two ports with the same name, after leveling up, they keep the same name