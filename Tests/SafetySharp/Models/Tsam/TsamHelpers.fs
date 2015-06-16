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
    
    let internal unnestBlocks (inputFile:string) = workflow {
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Models.TsamMutable.unnestBlocks ()
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
    let ``unnestBlocks applied on nestedBlocks1.sam returns a Stm without nested blocks `` () =
        let expectedResult =
            Block(StatementId 1,[])
            //Block (StatementId 1, [Write (StatementId 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 1)))); Choice (StatementId 3, [Block (StatementId 6, [Assume (StatementId 5,Literal (BoolVal false)); Write (StatementId 8,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 2))))]); Block (StatementId 10, [Assume (StatementId 9,Literal (BoolVal true)); Write (StatementId 12,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 4)))); Write (StatementId 13,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 8)))); Choice (StatementId 16, [Block (StatementId 19, [Assume (StatementId 18,Literal (BoolVal true)); Write (StatementId 22,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16)))); Write (StatementId 25,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 32)))); Write (StatementId 29,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 128)))); Write (StatementId 30,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64))))]); Block (StatementId 32, [Assume (StatementId 31,Literal (BoolVal false)); Write (StatementId 34,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64))))])]); Write (StatementId 36,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3))))])]); Write (StatementId 37,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (StatementId 40,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))]);
                    
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (unnestBlocks inputFile)
        printf "%s" modelString
        printf "%+A" model
        SafetySharp.Models.TsamChecks.hasBlocksNestedInBlocks (model.Body) =? false
        //model.Body =? expectedResult
        ()
        
    [<Test>]
    let ``unnestBlocks applied on nestedBlocks2.sam returns a Stm without nested blocks`` () =
        let expectedResult =
            Block(StatementId 1,[])
            //Block(StatementId 1, [Write (StatementId 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 1)))); Choice (StatementId 3, [Block(StatementId 6, [Assume (StatementId 5,Literal (BoolVal false)); Write (StatementId 8,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 2))))]); Block(StatementId 10, [Assume (StatementId 9,Literal (BoolVal true)); Write (StatementId 12,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 3)))); Write (StatementId 13,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 4)))); Stochastic (StatementId 15, [(Literal (ProbVal 0.2), Block(StatementId 16, [Write (StatementId 17,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 5))))])); (Literal (ProbVal 0.8), Block(StatementId 18, [Write (StatementId 19,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 6))))]))]); Choice (StatementId 21, [Block (StatementId 24, [Assume (StatementId 23,Literal (BoolVal true)); Write (StatementId 27,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 7)))); Stochastic (StatementId 28, [(Literal (ProbVal 0.1), Block(StatementId 29, [Write (StatementId 30,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 8))))])); (Literal (ProbVal 0.9), Block(StatementId 31,[Write (StatementId 32,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 9))))]))]); Write (StatementId 33,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 10)))); Write (StatementId 37,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 11)))); Write (StatementId 38,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 12))))]); Block(StatementId 40, [Assume (StatementId 39,Literal (BoolVal false)); Write (StatementId 42,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 13))))])]); Write (StatementId 44,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 14))))])]); Write (StatementId 45,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 15)))); Write (StatementId 48,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal ( bigint 16))))])
                    
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (unnestBlocks inputFile)
        printf "%s" modelString
        printf "%+A" model
        SafetySharp.Models.TsamChecks.hasBlocksNestedInBlocks (model.Body) =? false
        //model.Body =? expectedResult
        ()
                
    [<Test>]
    let ``treeify applied on nestedBlocks1.sam returns a treeified Stm`` () =
        //(example is Tsam Form of nestedBlocks2.sam)
        let expectedResult =
            Block(StatementId 1,[])
            //Block (StatementId 1, [Write (StatementId 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 1)))); Choice (StatementId 3, [Block (StatementId 52, [Assume (StatementId 53,Literal (BoolVal false)); Write (StatementId 54,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 2)))); Write (StatementId 55,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (StatementId 56,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))]); Block (StatementId 57, [Assume (StatementId 58,Literal (BoolVal true)); Write (StatementId 59,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 4)))); Write (StatementId 60,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 8)))); Choice (StatementId 61, [Block (StatementId 75, [Assume (StatementId 76,Literal (BoolVal true)); Write (StatementId 77,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16)))); Write (StatementId 78,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 32)))); Write (StatementId 79,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 128)))); Write (StatementId 80,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64)))); Write (StatementId 81,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3)))); Write (StatementId 82,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (StatementId 83,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))]); Block (StatementId 84, [Assume (StatementId 85,Literal (BoolVal false)); Write (StatementId 86,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 64)))); Write (StatementId 87,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3)))); Write (StatementId 88,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Write (StatementId 89,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7))))])])])])]);
        let inputFile = """../../Examples/SAM/nestedBlocks1.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (treeifyStm inputFile)
        printf "%s" modelString
        printf "%+A" model
        SafetySharp.Models.TsamChecks.isTreeForm (model.Body) =? true
        //model.Body =? expectedResult
        ()
                
    [<Test>]
    let ``treeify applied on nestedBlocks2.sam returns a treeified Stm `` () =
        //(example is Tsam Form of nestedBlocks2.sam)
        let expectedResult =
            Block(StatementId 1,[])
            //Block (StatementId 1, [Write (StatementId 2,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 1)))); Choice (StatementId 3, [Block (StatementId 85, [Assume (StatementId 86,Literal (BoolVal false)); Write (StatementId 87,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 2)))); Write (StatementId 88,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 15)))); Write (StatementId 89,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16))))]); Block (StatementId 90, [Assume (StatementId 91,Literal (BoolVal true)); Write (StatementId 92,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 3)))); Write (StatementId 93,Var "i",BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 4)))); Stochastic (StatementId 94, [(Literal (ProbVal 0.2), Block (StatementId 191, [Write (StatementId 192,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 5)))); Choice (StatementId 193, [Block (StatementId 251, [Assume (StatementId 252,Literal (BoolVal true)); Write (StatementId 253,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7)))); Stochastic (StatementId 254, [(Literal (ProbVal 0.1), Block (StatementId 311, [Write (StatementId 312,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 8)))); Write (StatementId 313,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (StatementId 314,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (StatementId 315,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (StatementId 316,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (StatementId 317,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (StatementId 318,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))])); (Literal (ProbVal 0.9), Block (StatementId 319, [Write (StatementId 320,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 9)))); Write (StatementId 321,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (StatementId 322,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (StatementId 323,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (StatementId 324,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (StatementId 325,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (StatementId 326,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))]))])]); Block (StatementId 269, [Assume (StatementId 270,Literal (BoolVal false)); Write (StatementId 271,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 13)))); Write (StatementId 272,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 14)))); Write (StatementId 273,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 15)))); Write (StatementId 274,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16))))])])])); (Literal (ProbVal 0.8), Block (StatementId 215, [Write (StatementId 216,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 6)))); Choice (StatementId 217, [Block (StatementId 287, [Assume (StatementId 288,Literal (BoolVal true)); Write (StatementId 289,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 7)))); Stochastic (StatementId 290, [(Literal (ProbVal 0.1), Block (StatementId 327, [Write (StatementId 328,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 8)))); Write (StatementId 329,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (StatementId 330,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (StatementId 331,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (StatementId 332,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (StatementId 333,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (StatementId 334,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))])); (Literal (ProbVal 0.9), Block (StatementId 335, [Write (StatementId 336,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 9)))); Write (StatementId 337,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 10)))); Write (StatementId 338,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 11)))); Write (StatementId 339,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 12)))); Write (StatementId 340,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 14)))); Write (StatementId 341,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 15)))); Write (StatementId 342,Var "i", BExpr (Read (Var "i"),Add, Literal (NumbVal (bigint 16))))]))])]); Block (StatementId 305, [Assume (StatementId 306,Literal (BoolVal false)); Write (StatementId 307,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 13)))); Write (StatementId 308,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 14)))); Write (StatementId 309,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 15)))); Write (StatementId 310,Var "i", BExpr (Read (Var "i"),Add,Literal (NumbVal (bigint 16))))])])]))])])])])
        let inputFile = """../../Examples/SAM/nestedBlocks2.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (treeifyStm inputFile)
        printf "%s" modelString
        printf "%+A" model
        SafetySharp.Models.TsamChecks.isTreeForm (model.Body) =? true
        //model.Body =? expectedResult
        ()