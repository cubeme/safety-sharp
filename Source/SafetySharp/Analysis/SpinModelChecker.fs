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

namespace SafetySharp.Analysis

open System
open SafetySharp
open SafetySharp.Modeling
open SafetySharp.Models

[<Sealed>]
type SpinModelChecker (model : Model) =
    do nullArg model "model"
    do model.FinalizeMetadata ()

    let ssm = model |> CilToSsm.transformModel
    do SsmValidation.validate model ssm
    let scm = ssm |> SsmLowering.lower model |> SsmToScm.transform
    do printf "%s" (ScmToString.toString scm)

//    member this.Check (formula : LtlFormula) =
//        let modelingAssembly = ModelingAssembly (model.GetType().Assembly)
//        let formulas = [formula.Formula]
//        let configuration = ModelTransformation.Transform modelingAssembly.Compilation model formulas
//        
//        let converter = SafetySharp.Analysis.Modelchecking.PromelaSpin.MetamodelToPromela configuration
//        let astWriter = SafetySharp.Analysis.Modelchecking.PromelaSpin.ExportPromelaAstToFile ()
//
//        let converted = converter.transformConfiguration
//        FileSystem.WriteToAsciiFile "Modelchecking/Spin.promela" (astWriter.Export converted)
//
//        let converter = SafetySharp.Analysis.Modelchecking.NuXmv.MetamodelToNuXmv configuration
//        let astWriter = SafetySharp.Analysis.Modelchecking.NuXmv.ExportNuXmvAstToFile ()
//
//        let converted = converter.transformConfiguration
//        FileSystem.WriteToAsciiFile "Modelchecking/NuXmv.smv" (astWriter.ExportNuXmvProgram converted)

//        ()