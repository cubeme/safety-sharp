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

module AstTestHelpers

open System
open NUnit.Framework

open SafetySharp.Internal.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult

let internal selectAst = function
    | Ast(ast) -> ast :> obj 
    | Error(e) -> Assert.Fail(e); null
    
let internal selectParseError = function
    | Error(_) -> true :> obj
    | _ -> Assert.Fail("Parsing succeeded even though error was expected."); false :> obj


let internal inAst<'a> ast = ParsingResult<'a>.Ast(ast)

type internal Invalid = | InvalidAst

let internal failsParsing = function
    | Error(_) -> ()
    | _ -> Assert.Fail("Parsing succeeded even though error was expected."); // TODO:ObjectDumper

let internal anyAstOfType<'a> (ast:ParsingResult<'a>)=
    match ast with     
        | ParsingResult.Ast(ast) -> ()
        | ParsingResult.Error(e) -> Assert.Fail(e)


(*
let anyAstOfType<'a> = function
    | Ast(ast) ->
        match box ast with
            | :? 'a as correctType -> ()
            | _                    -> Assert.Fail("Wrong type")
    | Error(e) ->
            Assert.Fail(e)
*)

(*
let returnAst<'a> ast = new SelectorEqualConstraint<ParsingResult<'a>>(selectAst, ast)

let invalid<'a> = new SelectorEqualConstraint<ParsingResult<'a>>(selectParseError, true)

// example usage: 
//        parseTerm exampleFormula1String |> should be anyAstOfTypeTerm
let anyAstOfType<'a> = 
    let selectAst = function
        | Ast(ast) -> match box ast with
                        | :? 'a as correctType -> true :> obj
                        | _                    -> false :> obj
        | Error(e) -> Assert.Fail(e); false :> obj
    new SelectorEqualConstraint<ParsingResult<'a>>(selectAst, true)

//let beOfKind kind = new SelectorEqualConstraint<SemanticAnalysisResult<Kind>>(selectKind, kind)

*)