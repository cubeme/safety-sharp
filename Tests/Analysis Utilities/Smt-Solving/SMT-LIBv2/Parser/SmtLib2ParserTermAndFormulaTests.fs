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

namespace SafetySharp.SmtSolving.SmtLib2.Parser

open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers
open SafetySharp.Analysis.SmtSolving.SmtLib2.Ast
open SafetySharp.Analysis.SmtSolving.SmtLib2.Parser
open SafetySharp.Analysis.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult

type SMTTermAndFormulasExampleTests() =
    let parser = new SMTCommonParser()
    
    let inAstFloat = inAst<float>
    let inAstTerm  = inAst<Term>
    let anyAstOfTypeTerm = anyAstOfType<Term>

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> (Ast result)
        | Failure(errorMsg, _, _) -> (Error errorMsg)
        
    let parseFloat str = parseWithParser pfloat str
    let parseTerm  str = parseWithParser (parser.parseTerm .>> eof) str
    
    let exampleSimpleForallString = 
        "( forall ( ( x  Int ) ( y  Int ) ) 5 )"
    let exampleSimpleForallAst =
        ( Term.TermForAllTerm([ Symbol.Symbol("x"), Sort.SortSimple(Identifier.IdSymbol(Symbol.Symbol("Int"))) ;
                                Symbol.Symbol("y"), Sort.SortSimple(Identifier.IdSymbol(Symbol.Symbol("Int")))
                            ], Term.TermSpecConstant(SpecConstant.SpecConstantNumeral(new bigint(5)))
                            )
        )

    let exampleSimpleImpliesString =
        "(=> ( and ( r x0 x1 ) ( r x1 x2 ) ) )"
    let exampleSimpleImpliesAst =
        ( Term.TermQualIdTerm( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("=>"))),
                                [ Term.TermQualIdTerm
                                   ( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("and"))),
                                                   [
                                                       Term.TermQualIdTerm(
                                                                           QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("r"))),
                                                                           [ Term.TermQualIdentifier( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("x0"))));
                                                                             Term.TermQualIdentifier( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("x1"))))
                                                                           ]             
                                                                       );
                                                       Term.TermQualIdTerm(
                                                                           QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("r"))),
                                                                           [ Term.TermQualIdentifier( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("x1"))));
                                                                             Term.TermQualIdentifier( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("x2"))))
                                                                           ]             
                                                                       )
                                                   ]
                                   )
                                ]
                            )
        )

    let exampleSimpleAttributedString = 
        "(=> ( ! x :named $p1 ) )"
    let exampleSimpleAttributedAst = 
        ( Term.TermQualIdTerm( QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("=>"))),
                               [Term.TermExclimationPt( Term.TermQualIdentifier(QualIdentifier(Identifier.IdSymbol(Symbol.Symbol("x")))),
                                                        [ Attribute.AttributeKeywordWithValue(Keyword.Keyword("named"),
                                                                                              AttributeValue.AttributeValueSymbol(Symbol.Symbol("$p1"))
                                                                                             )
                                                        ]
                                                      )
                               ]
                             )
        )

    let exampleInvalidAttributedString = 
        "(=> ( ! x ) :named $p1 )"
        
    let exampleDoubleAttributedString =
        "(! x :pattern ( ( r x0 x1 ) ( r x1 x2 ) ) :pattern ( ( p x0 a ) ) )"

    let exampleSExprAttributedString =
        "(! x :pattern ( ( r x0 x1 ) ( r x1 x2 ) ) )"

    let exampleFormula1String =
        "( forall ( ( x ( List Int ) ) ( y ( List Int ) ) )\n(= ( append x y )\n( ite (= x ( as nil ( List Int ) ) )\ny\n( let ( ( h ( head x ) ) ( t ( tail x ) ) )\n( insert h ( append t y ) ) ) ) ) )\n"

    let exampleFormula2String =
        "(=> ( ! (> x y ) :named $p1 )\n( ! (= x z ) :named $p2 ) )"

    let exampleFormula3String =
        "( forall ( ( x0 A ) ( x1 A ) ( x2 A ) )\n( ! (=> ( and ( r x0 x1 ) ( r x1 x2 ) ) ( r x0 x2 ) )\n:pattern ( ( r x0 x1 ) ( r x1 x2 ) )\n:pattern ( ( p x0 a ) )\n) )\n"


    [<Test>]
    member this.``Datastructure ParsingResult works with convenience function returnAstFloat``() =
        (ParsingResult<float>.Ast 1.25) =? inAstFloat 1.25

    [<Test>]
    member this.``a simple float should parse correctly``() =
        parseFloat "1.25" =? inAstFloat 1.25

    [<Test>]
    member this.``example formula 1 should just parse at all``() =
        parseTerm exampleFormula1String |> anyAstOfTypeTerm

    [<Test>]
    member this.``example formula 2 should just parse at all``() =
        parseTerm exampleFormula2String |> anyAstOfTypeTerm

    [<Test>]
    member this.``example formula 3 should just parse at all``() =
        parseTerm exampleFormula3String |> anyAstOfTypeTerm
                
    [<Test>]
    member this.``a simple term with forall should be parsed correctly``() =
        parseTerm exampleSimpleForallString =? inAstTerm exampleSimpleForallAst

    [<Test>]
    member this.``a simple term with an "=>" should be parsed correctly``() =
        parseTerm exampleSimpleImpliesString =? inAstTerm exampleSimpleImpliesAst
        
    [<Test>]
    member this.``a simple term which is attributed by an "!" should be parsed correctly``() =
        parseTerm exampleSimpleAttributedString =? inAstTerm exampleSimpleAttributedAst
                
    [<Test>]
    member this.``a simple term which is attributed incorrectly "!" shouldn't be parsed``() =
        parseTerm exampleInvalidAttributedString |> failsParsing
        
    [<Test>]
    member this.``a term which is attributed by an "!" with an sexpr-attribute should be parsed correctly``() =
        parseTerm exampleSExprAttributedString |> anyAstOfTypeTerm

    [<Test>]
    member this.``a term which is attributed by an "!" with two attributes should be parsed correctly``() =
        parseTerm exampleDoubleAttributedString |> anyAstOfTypeTerm
                    
        