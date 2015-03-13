// The MIT License (MIT)
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

namespace SafetySharp.Tests.Modelchecking.Promela.PromelaTransformSamTests

open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers

open SafetySharp.Analysis.Modelchecking.PromelaSpin



[<TestFixture>]
module SamToPromelaTests =

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg

    let internal parseSam str = parseWithParser (SafetySharp.Models.SamParser.samFile .>> eof) str

    let internal promelaWriter = PromelaToString()
    
           
    [<Test>]
    let ``simpleBoolean1.sam gets converted to promela`` () =
        
        let inputFile = """../../Examples/SAM/simpleBoolean1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSam input
        let promela = SamToPromela.transformConfiguration model

        let promelaCodeString = promelaWriter.Export promela
        printf "%s" promelaCodeString
        ()
           
    [<Test>]
    let ``smokeTest1.sam gets converted to promela`` () =
        
        let inputFile = """../../Examples/SAM/smokeTest1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSam input
        let promela = SamToPromela.transformConfiguration model

        let promelaCodeString = promelaWriter.Export promela
        printf "%s" promelaCodeString
        ()
