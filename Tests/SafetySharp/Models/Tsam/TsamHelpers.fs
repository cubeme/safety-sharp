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

namespace Models.Tsam

open NUnit.Framework
open SafetySharp.Workflow
open SafetySharp.Models


// To quickly generate "let expectedResults =":
//  * Use 'printf "%+A"
//  * Ctrl+C output
//  * Ctrl+V in code
//  * Select
//  * Ctrl+H, enable Regular expressions, find "NumbVal (\d+)" replace by "NumbVal (bigint $1)"
//  * Select
//  * Ctrl+H, enable Regular expressions, find "\s+" replace by " "

// https://msdn.microsoft.com/en-us/library/2k3te2cs(v=vs.110).aspx
// include "([a-zA-Z]+\.h)", replace with include <$1>

[<TestFixture>]
module TsamHelpers =
    open SafetySharp.Models.Sam
    open SafetySharp.Models.Tsam
    
    let internal normalizeBlocks (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamMutable.normalizeBlocks ()
            let! model = SafetySharp.Models.TsamMutable.getTsamModel ()
            do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
            let! modelString = getState ()
            return (model,modelString)
        }

    let internal treeifyStm (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamMutable.treeifyStm ()
            let! model = SafetySharp.Models.TsamMutable.getTsamModel ()
            do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
            let! modelString = getState ()
            return (model,modelString)
        }
        
    [<Test>]
    let ``normalizeBlocks applied on nestedBlocks1.sam returns a Stm without nested blocks `` () =
        let expectedResult =
            Block (Some 1, [Write (Some 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 1)))); Choice (Some 3, [Block (Some 6, [Assume (Some 5,Literal (BoolVal false)); Write (Some 8,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 2))))]); Block (Some 10, [Assume (Some 9,Literal (BoolVal true)); Write (Some 12,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 4)))); Write (Some 13,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 8)))); Choice (Some 16, [Block (Some 19, [Assume (Some 18,Literal (BoolVal true)); Write (Some 22,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16)))); Write (Some 25,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 32)))); Write (Some 29,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 128)))); Write (Some 30,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64))))]); Block (Some 32, [Assume (Some 31,Literal (BoolVal false)); Write (Some 34,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64))))])]); Write (Some 36,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3))))])]); Write (Some 37,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (Some 40,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))]);
                    
        let treeifyAndNormalize = workflow {
            do! SafetySharp.Models.TsamMutable.treeifyStm ()
            do! SafetySharp.Models.TsamMutable.normalizeBlocks ()
        }
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (normalizeBlocks inputFile)
        printf "%s" modelString
        printf "%+A" model
        model.Body =? expectedResult
        ()
        
    [<Test>]
    let ``normalizeBlocks applied on nestedBlocks2.sam returns a Stm without nested blocks`` () =
        let expectedResult =
            Block(Some 1, [Write (Some 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 1)))); Choice (Some 3, [Block(Some 6, [Assume (Some 5,Literal (BoolVal false)); Write (Some 8,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 2))))]); Block(Some 10, [Assume (Some 9,Literal (BoolVal true)); Write (Some 12,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 3)))); Write (Some 13,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 4)))); Stochastic (Some 15, [(Literal (ProbVal 2.0), Block(Some 16, [Write (Some 17,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 5))))])); (Literal (ProbVal 8.0), Block(Some 18, [Write (Some 19,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 6))))]))]); Choice (Some 21, [Block (Some 24, [Assume (Some 23,Literal (BoolVal true)); Write (Some 27,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 7)))); Stochastic (Some 28, [(Literal (ProbVal 1.0), Block(Some 29, [Write (Some 30,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 8))))])); (Literal (ProbVal 9.0), Block(Some 31,[Write (Some 32,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 9))))]))]); Write (Some 33,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 10)))); Write (Some 37,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 11)))); Write (Some 38,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 12))))]); Block(Some 40, [Assume (Some 39,Literal (BoolVal false)); Write (Some 42,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 13))))])]); Write (Some 44,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 14))))])]); Write (Some 45,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 15)))); Write (Some 48,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 16))))])
                    
        let treeifyAndNormalize = workflow {
            do! SafetySharp.Models.TsamMutable.treeifyStm ()
            do! SafetySharp.Models.TsamMutable.normalizeBlocks ()
        }
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (normalizeBlocks inputFile)
        printf "%s" modelString
        printf "%+A" model
        model.Body =? expectedResult
        ()
                
    [<Test>]
    let ``treeify applied on nestedBlocks1.sam returns a Stm without blocks with `` () =
        //(example is Tsam Form of nestedBlocks2.sam)
        let expectedResult =
            Block (Some 1, [Write (Some 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 1)))); Choice (Some 3, [Block (Some 52, [Assume (Some 53,Literal (BoolVal false)); Write (Some 54,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 2)))); Write (Some 55,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (Some 56,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))]); Block (Some 57, [Assume (Some 58,Literal (BoolVal true)); Write (Some 59,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 4)))); Write (Some 60,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 8)))); Choice (Some 61, [Block (Some 75, [Assume (Some 76,Literal (BoolVal true)); Write (Some 77,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16)))); Write (Some 78,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 32)))); Write (Some 79,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 128)))); Write (Some 80,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64)))); Write (Some 81,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3)))); Write (Some 82,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (Some 83,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))]); Block (Some 84, [Assume (Some 85,Literal (BoolVal false)); Write (Some 86,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64)))); Write (Some 87,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3)))); Write (Some 88,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (Some 89,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))])])])])]);
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (treeifyStm inputFile)
        printf "%s" modelString
        printf "%+A" model
        model.Body =? expectedResult
        ()
                
    [<Test>]
    let ``treeify applied on nestedBlocks2.sam returns a Stm without blocks with `` () =
        //(example is Tsam Form of nestedBlocks2.sam)
        let expectedResult =
            Block (Some 1, [Write (Some 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 1)))); Choice (Some 3, [Block (Some 85, [Assume (Some 86,Literal (BoolVal false)); Write (Some 87,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 2)))); Write (Some 88,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 15)))); Write (Some 89,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16))))]); Block (Some 90, [Assume (Some 91,Literal (BoolVal true)); Write (Some 92,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3)))); Write (Some 93,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 4)))); Stochastic (Some 94, [(Literal (ProbVal 2.0), Block (Some 191, [Write (Some 192,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Choice (Some 193, [Block (Some 251, [Assume (Some 252,Literal (BoolVal true)); Write (Some 253,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7)))); Stochastic (Some 254, [(Literal (ProbVal 1.0), Block (Some 311, [Write (Some 312,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 8)))); Write (Some 313,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (Some 314,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (Some 315,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (Some 316,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (Some 317,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (Some 318,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))])); (Literal (ProbVal 9.0), Block (Some 319, [Write (Some 320,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 9)))); Write (Some 321,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (Some 322,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (Some 323,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (Some 324,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (Some 325,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (Some 326,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))]))])]); Block (Some 269, [Assume (Some 270,Literal (BoolVal false)); Write (Some 271,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 13)))); Write (Some 272,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 14)))); Write (Some 273,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 15)))); Write (Some 274,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16))))])])])); (Literal (ProbVal 8.0), Block (Some 215, [Write (Some 216,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 6)))); Choice (Some 217, [Block (Some 287, [Assume (Some 288,Literal (BoolVal true)); Write (Some 289,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7)))); Stochastic (Some 290, [(Literal (ProbVal 1.0), Block (Some 327, [Write (Some 328,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 8)))); Write (Some 329,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (Some 330,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (Some 331,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (Some 332,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (Some 333,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (Some 334,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))])); (Literal (ProbVal 9.0), Block (Some 335, [Write (Some 336,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 9)))); Write (Some 337,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (Some 338,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (Some 339,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (Some 340,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (Some 341,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (Some 342,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))]))])]); Block (Some 305, [Assume (Some 306,Literal (BoolVal false)); Write (Some 307,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 13)))); Write (Some 308,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 14)))); Write (Some 309,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 15)))); Write (Some 310,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16))))])])]))])])])])
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (treeifyStm inputFile)
        printf "%s" modelString
        printf "%+A" model
        model.Body =? expectedResult
        ()