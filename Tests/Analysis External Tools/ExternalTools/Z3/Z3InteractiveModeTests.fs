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

namespace SafetySharp.ExternalTools

open System
open NUnit.Framework
open AstTestHelpers
open SafetySharp.Analysis.SmtSolving.SmtLib2.Ast
open SafetySharp.Analysis.SmtSolving.SmtLib2.SmtShortTypes
open SafetySharp.Analysis.SmtSolving.Z3.Execute

type Z3InteractiveModeTests() = 
    
    let isOfTypeSExpr obj =
        match box obj with
                            | :? Smt2SExpr as correctType -> true
                            | _                           -> false

    [<Test>]
    member this.``interactive mode works (start,help,quit)``() =
        let z3 = new ExecuteZ3Interactive()
        z3.Start ()
        let output = z3.ExecuteCustomCommand "(help)"
        z3.Shutdown ()
        isOfTypeSExpr output  =? true