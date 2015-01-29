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

namespace SafetySharp.Tests.Modelchecking.NuXmv.NuXmvTransformMetamodelTests


open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers

open SafetySharp.Internal.Modelchecking.NuXmv



[<TestFixture>]
module SamToNuXmvTests =

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg

    let internal parseSam str = parseWithParser (SafetySharp.Models.Sam.Parser.samFile .>> eof) str

    let internal nuXmvWriter = ExportNuXmvAstToFile()

           
    [<Test>]
    let ``simpleBoolean1.sam gets converted to nuXmv`` () =
        
        let inputFile = """../../Examples/SAM/simpleBoolean1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let model = parseSam input
        let nuXmv = SamToNuXmv.transformConfiguration model

        let nuXmvCodeString = nuXmvWriter.ExportNuXmvProgram nuXmv
        printf "%s" nuXmvCodeString
        ()
