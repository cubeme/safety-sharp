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

namespace SafetySharp.Modelchecking

open NUnit.Framework

module BoogieSmokeTests =
    open SafetySharp.Models
    open SafetySharp.Workflow
    open SafetySharp.ITracing


    let internal smokeTestWorkflow (inputFile:string) = workflow {    
            do! readFile inputFile
            do! SafetySharp.Models.SamParser.parseStringWorkflow
            do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            do! SafetySharp.Analysis.Modelchecking.Boogie.TsamToBoogie.transformVcSamToBoogieWf ()
            do! logForwardTracesOfOrigins ()
            do! SafetySharp.ITracing.removeTracing ()
            do! SafetySharp.Analysis.Modelchecking.Boogie.BoogieToString.boogieToStringWf ()
            //let filename = sprintf "%s.bpl" (System.IO.Path.GetFileName(inputFile) ) |> SafetySharp.FileSystem.FileName
            //do! saveToFile filename
            //do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPan
    }
    
    let runSmokeTest (inputFile) =
        SafetySharp.Workflow.runWorkflow_getState (smokeTestWorkflow inputFile)
        
    [<Test>]
    let ``smokeTest1.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest1.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest2.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest2.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest3.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest3.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest4.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest4.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest5.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest5.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest6.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest6.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest7.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest7.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest8.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest8.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest9.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest9.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest10.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest10.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest11.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest11.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest12.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest12.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest13.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest13.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest14.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest14.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest15.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest15.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest16.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest16.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest17.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest17.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest18.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest18.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest19.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest19.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest20.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest20.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest21.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest21.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest22.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest22.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``smokeTest23.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/smokeTest23.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``reserved names do not make any problems`` () =        
        let inputFile = """../../Examples/SAM/reservedNames.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntError1.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntError1.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntError2.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntError2.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntWrapAround1.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntWrapAround1.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntWrapAround2.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntWrapAround2.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntWrapAround3.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntWrapAround3.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntWrapAround4.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntWrapAround4.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntClamp1.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntClamp1.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()

    [<Test>]
    let ``overflowIntClamp2.sam returns the expected results`` () =        
        let inputFile = """../../Examples/SAM/overflowIntClamp2.sam"""
        let output = runSmokeTest inputFile
        printf "%s" output
        ()