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

[<TestFixture>]
type ExtensionMethods () =


    let runWithUserState parser str = runParserOnString parser ScmParser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (ScmParser.scmFile .>> eof) str
            
    [<Test>]
    member this.``Nested Component in nestedComponent2 gets found`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let path = Comp("nested_n22") :: Comp("nested_n2") :: Comp("simple") :: []
        let subNode = model.getDescendantUsingPath path
        subNode.Comp =? Comp("nested_n22")
        ()
          
    [<Test>]
    member this.``Parent of Nested Component in nestedComponent2 gets found`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let path = Comp("nested_n22") :: Comp("nested_n2") :: Comp("simple") :: []
        let parentPath = path.Tail
        let subNode = model.getDescendantUsingPath parentPath
        subNode.Comp =? Comp("nested_n2")
        ()
          
    [<Test>]
    member this.``Sub Component in nestedComponent2 gets found`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let path = Comp("nested_n2") :: Comp("simple") :: []
        let subNode = model.getDescendantUsingPath path
        subNode.Comp =? Comp("nested_n2")
        ()
                
    [<Test>]
    member this.``Parent of Sub Component in nestedComponent2 gets found`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let path = Comp("nested_n2") :: Comp("simple") :: []
        let parentPath = path.Tail
        let subNode = model.getDescendantUsingPath  parentPath
        subNode.Comp =? Comp("simple")
        ()
          

    [<Test>]
    member this.``Parent node can be replaced`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathTarget = Comp("simple") :: []
        let pathSource = Comp("nested_n2") :: Comp("simple") :: []
        let nodeSource = model.getDescendantUsingPath  pathSource
        let newModel = model.replaceDescendant  pathTarget nodeSource
        printf "%+A" newModel
        let newModelPath = Comp("nested_n2") :: []
        let newModelNode = newModel.getDescendantUsingPath newModelPath
        newModelNode.Comp =? Comp("nested_n2")
        ()
          
    [<Test>]
    member this.``Sub node can be replaced`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathTarget =Comp("nested_n1") :: Comp("simple") :: []
        let pathSource = Comp("nested_n22") :: Comp("nested_n2") :: Comp("simple") :: []
        let nodeSource = model.getDescendantUsingPath pathSource
        let newModel = model.replaceDescendant pathTarget nodeSource
        printf "%+A" newModel
        let newModelPath = Comp("nested_n22") :: Comp("simple") :: []
        let newModelNode = newModel.getDescendantUsingPath newModelPath
        newModelNode.Comp =? Comp("nested_n22")
        ()

    [<Test>]
    member this.``Nested node can be replaced`` () =
        let inputFile = """../../Examples/SCM/nestedComponent2.scm"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSCM input
        let pathTarget = Comp("nested_n12") :: Comp("nested_n1") :: Comp("simple") :: []
        let pathSource = Comp("nested_n2") :: Comp("simple") :: []
        let nodeSource = model.getDescendantUsingPath pathSource
        let newModel = model.replaceDescendant pathTarget nodeSource
        printf "%+A" newModel
        let newModelPath = Comp("nested_n22") :: Comp("nested_n2") :: Comp("nested_n1") :: Comp("simple"):: []
        let newModelNode = newModel.getDescendantUsingPath newModelPath
        newModelNode.Comp =? Comp("nested_n22")
        ()
          

