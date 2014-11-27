﻿// The MIT License (MIT)
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

namespace SafetySharp.Tests.FIL.FILParserTests


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

    let parseFIL str = parseWithParser (SafetySharp.Internal.FIL.Parser.ParseFIL.filFile) str

    [<Test>]
    member this.``Example simpleArithmetical1 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleArithmetical1.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleArithmetical2 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleArithmetical2.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleBoolean1 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleBoolean1.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands1 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleGuardedCommands1.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands2 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleGuardedCommands2.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands3 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleGuardedCommands3.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simpleGuardedCommands4 parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simpleGuardedCommands4.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()

    [<Test>]
    member this.``Example simplePrev parses correctly`` () =
        let inputFile = """..\..\Examples\FIL\simplePrev.fil"""
        let input = System.IO.File.ReadAllText inputFile
        let result = parseFIL input
        ()
