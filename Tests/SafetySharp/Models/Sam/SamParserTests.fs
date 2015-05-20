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

namespace Models.Sam


open System
open NUnit.Framework
open FParsec

open TestHelpers
open AstTestHelpers

[<TestFixture>]
type ExampleFiles() =

    let parseWithParser parser str =
        match run parser str with
        | Success(result, _, _)   -> result
        | Failure(errorMsg, _, _) -> failwith errorMsg

    let parseSam str = parseWithParser (SafetySharp.Models.SamParser.samFile .>> eof) str

    [<Test>]
    member this.``Example simpleArithmetical1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleArithmetical1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simpleArithmetical2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleArithmetical2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simpleBoolean1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleBoolean1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands3 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands3.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands4 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands4.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example simplePrev parses successfully`` () =
        let inputFile = """../../Examples/SAM/simplePrev.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example nestedBlocks1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example nestedBlocks2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest3 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest3.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest4 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest4.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest5 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest5.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest6 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest6.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest7 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest7.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest8 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest8.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest9 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest9.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest10 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest10.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest11 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest11.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest12 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest12.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest13 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest13.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest14 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest14.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest15 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest15.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest16 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest16.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest17 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest17.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest18 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest18.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest19 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest19.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest20 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest20.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest21 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest21.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest22 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest22.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example smokeTest23 parses successfully`` () =
        let inputFile = """../../Examples/SAM/smokeTest23.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example reservedNames parses successfully`` () =
        let inputFile = """../../Examples/SAM/reservedNames.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntError1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntError1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntError2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntError2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntWrapAround1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntWrapAround1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntWrapAround2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntWrapAround2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntWrapAround3 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntWrapAround3.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntWrapAround4 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntWrapAround4.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntClamp1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntClamp1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()

    [<Test>]
    member this.``Example overflowIntClamp2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/overflowIntClamp2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseSam input
        ()