// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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
open ScmRewriter

[<TestFixture>]
type SingleRewriterTests () =

    let runWithUserState parser str = runParserOnString parser Parser.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, a, b) -> failwith errorMsg
        
    let parseSCM str = parseWithParser (Parser.scmFile .>> eof) str
            
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
        let initialState =
            {
                ScmRewriteState.Model = model;
                ScmRewriteState.ComponentToRemove = Some(pathOfChild);
                ScmRewriteState.Tainted = false;
            }
        let (_,resultingState) = ScmRewriter.runState ScmRewriter.levelUpField initialState
        let newModel = resultingState.Model
        let newChildNode = newModel.getDescendantUsingPath pathOfChild
        let newParentNode = newModel.getDescendantUsingPath pathOfParent
        printf "%+A" newModel
        resultingState.Tainted =? true
        newChildNode.Fields.Length =? 0
        newParentNode.Fields.Length =? 2        
        ()
          