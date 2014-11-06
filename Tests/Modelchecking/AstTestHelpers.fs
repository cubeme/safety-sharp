module internal AstTestHelpers

open System
open NUnit.Framework

open SafetySharp.Internal.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult

let selectAst = function
    | Ast(ast) -> ast :> obj 
    | Error(e) -> Assert.Fail(e); null
    
let selectParseError = function
    | Error(_) -> true :> obj
    | _ -> Assert.Fail("Parsing succeeded even though error was expected."); false :> obj


let inAst<'a> ast = ParsingResult<'a>.Ast(ast)

type Invalid = | InvalidAst

let failsParsing = function
    | Error(_) -> ()
    | _ -> Assert.Fail("Parsing succeeded even though error was expected."); // TODO:ObjectDumper

let anyAstOfType<'a> (ast:ParsingResult<'a>)=
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