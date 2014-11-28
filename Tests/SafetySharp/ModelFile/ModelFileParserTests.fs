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

namespace SafetySharp.Tests.ModelFile.ModelFileParserTests


open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers
open SafetySharp.Internal.ModelFile.Parser
open Test

[<TestFixture>]
type ParsingUserStateWorks () =

    let runWithUserState parser str = runParserOnString parser ParseModelFile.UserState.initialUserState "" str
    
    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg
        
    let parseVarIdDecl str = parseWithParser (ParseModelFile.varIdDecl ) str
    let parseVarIdInst str = parseWithParser (ParseModelFile.varIdInst ) str

    
    [<Test>]
    member this.``Field declaration has an effect on the user state of the parser`` () =
        let customParser = ParseModelFile.varIdDecl .>>. (spaces >>. ParseModelFile.varIdInst .>> eof)
        
        let input = "int1Var int1Var"
        let fullResult = runWithUserState customParser input
        match fullResult with
            | Success(result, userState, _)   ->
                let (decl,inst) = result
                decl =? Var.Var("int1Var")
                inst =? Var.Var("int1Var")
                userState.IsIdentifierOfType "int1Var" ParseModelFile.IdentifierType.Var =? true
            | Failure(errorMsg, _, _) -> failwith errorMsg
        ()



(*
[<TestFixture>]
type ExampleFiles() =

    let runWithUserState parser str = runParserOnString parser SafetySharp.Internal.ModelFile.Parser.ParseModelFile.UserState.initialUserState "" str

    let parseWithParser parser str =
        match runWithUserState parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg

    let parseFIL str = parseWithParser (SafetySharp.Internal.FIL.Parser.ParseFIL.filFile .>> eof) str

    [<Test>]
    member this.``Example simpleArithmetical1 parses successfully`` () =
        let inputFile = """..\..\Examples\FIL\simpleArithmetical1.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()
*)