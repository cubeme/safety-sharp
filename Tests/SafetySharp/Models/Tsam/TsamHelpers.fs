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

    [<Test>]
    let ``normalizeBlocks returns a Stm without nested blocks`` () =
        //(example is Tsam Form of nestedBlocks.sam)
        let inputFile = """../../Examples/SAM/nestedBlocks.sam"""        
        let (model,modelString) = SafetySharp.Workflow.runWorkflow_getResult (normalizeBlocks inputFile)
        printf "%s" modelString
        printf "%+A" model
        ()


