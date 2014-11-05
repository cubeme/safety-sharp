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

namespace SMTLIB2Parser.Tests

open System
open NUnit.Framework
open FParsec

open TestHelpers
open SMTLIB2DataStructures.Ast
open AstTestHelpers
open SmtLib2ParsingResult

type SMTAttributesExampleTests() =
    let parser = new SMTLIB2Parser.SMTCommonParser()
    
    let inAstFloat = inAst<float>
    let inAstAttribute  = inAst<Attribute>

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> (Ast result)
        | Failure(errorMsg, _, _) -> (Error errorMsg)
        
    let parseFloat str = parseWithParser pfloat str
    let parseAttribute  str = parseWithParser (parser.parseAttribute .>> eof) str
    
    let exampleAttribute1String = 
        ":named $p1"
    let exampleAttributeAst =
        Attribute.AttributeKeywordWithValue(Keyword.Keyword("named"),
                                            AttributeValue.AttributeValueSymbol(Symbol.Symbol("$p1"))
                                           )
        
    let exampleAttribute2String =
        ":pattern ( ( r x0 x1 ) ( r x1 x2 ) )"
    let exampleAttribute2Ast =
        Attribute.AttributeKeywordWithValue(Keyword.Keyword("pattern"),
                                            AttributeValue.AttributeValueSExprList([ SExpr.SExprSExprList [SExpr.SExprSymbol(Symbol.Symbol("r"));SExpr.SExprSymbol(Symbol.Symbol("x0"));SExpr.SExprSymbol(Symbol.Symbol("x1"))];
                                                                                     SExpr.SExprSExprList [SExpr.SExprSymbol(Symbol.Symbol("r"));SExpr.SExprSymbol(Symbol.Symbol("x1"));SExpr.SExprSymbol(Symbol.Symbol("x2"))]
                                                                                   ])
                                           )

    let exampleAttribute3String =
        ":pattern ( ( p x0 a ) )"
    let exampleAttribute3Ast =
        Attribute.AttributeKeywordWithValue(Keyword.Keyword("pattern"),
                                            AttributeValue.AttributeValueSExprList([ SExpr.SExprSExprList [SExpr.SExprSymbol(Symbol.Symbol("p"));SExpr.SExprSymbol(Symbol.Symbol("x0"));SExpr.SExprSymbol(Symbol.Symbol("a"))]
                                                                                   ])
                                           )

    [<Test>]
    member this.``Datastructure ParsingResult works with convenience function returnAstFloat``() =
        (ParsingResult<float>.Ast 1.25) =? inAstFloat 1.25

    [<Test>]
    member this.``a simple float should parse correctly``() =
        parseFloat "1.25" =? inAstFloat 1.25
        
    [<Test>]
    member this.``a simple attribute should be parsed correctly``() =
        parseAttribute exampleAttribute1String =? inAstAttribute exampleAttributeAst
        
    [<Test>]
    member this.``a simple attribute ":pattern ( ( r x0 x1 ) ( r x1 x2 ) )" should be parsed``() =
        parseAttribute exampleAttribute2String =? inAstAttribute exampleAttribute2Ast
                
    [<Test>]
    member this.``a simple attribute ":pattern ( ( p x0 a ) ) )" should be parsed``() =
        parseAttribute exampleAttribute3String =? inAstAttribute exampleAttribute3Ast