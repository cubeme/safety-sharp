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

namespace SafetySharp.Tests.Models.Sam.ParserTests


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

    let parseFIL str = parseWithParser (SafetySharp.Models.Sam.Parser.samFile .>> eof) str

    [<Test>]
    member this.``Example simpleArithmetical1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleArithmetical1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleArithmetical2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleArithmetical2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleBoolean1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleBoolean1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands1 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands1.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands2 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands2.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands3 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands3.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands4 parses successfully`` () =
        let inputFile = """../../Examples/SAM/simpleGuardedCommands4.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simplePrev parses successfully`` () =
        let inputFile = """../../Examples/SAM/simplePrev.sam"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()
