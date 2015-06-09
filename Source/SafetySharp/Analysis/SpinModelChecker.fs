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
open SafetySharp.Runtime.Modeling
open SafetySharp.Models
open SafetySharp.Analysis.Modelchecking.PromelaSpin
open SafetySharp.Workflow

[<Sealed>]
type SpinModelChecker (model : Model) =
    do nullArg model "model"
    do model.FinalizeMetadata ()

    let scmRootComp = 
        model 
        |> CilToSsm.transformModel 
        |> SsmLowering.lowerPreValidation model
        |> SsmValidation.validate model
        |> SsmLowering.lowerPostValidation model 
        |> SsmToScm.transform

    do printf "%s" (ScmToString.toString scmRootComp)
    let scm = scmRootComp |> Scm.ScmModel
   // do printf "======================================="
   
   (*
    let workflowToExecute : WorkflowFunction<_,_,unit> = workflow {
            do! ScmMutable.setInitialPlainModelState scm
            do! ScmToPromela.transformConfiguration ()
            do! SafetySharp.ITracing.logForwardTracesOfOrigins()
            return ()
        }
    let spin = runWorkflow_getState workflowToExecute

    //do printf "%+A" spin
    let spinWriter = SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString()
    let spincode = spinWriter.Export (spin.PrSpec)
    do printf "%s" spincode
    *)

    let tankComp = [Scm.Comp("Tank0@0");Scm.Comp("R")]
    let tankPressure = tankComp,Scm.Field("_pressureLevel$$")
    let value60 = ScmVerificationElements.PropositionalExpr.Literal(Scm.Val.IntVal(60))
    let hazard = ScmVerificationElements.PropositionalExpr.BExpr( ScmVerificationElements.PropositionalExpr.ReadField(tankPressure),Scm.BOp.GreaterEqual, value60)

    let ltlDcca = SafetySharp.Analysis.Techniques.AtDccaLtl.PerformDccaWithLtlFormulas(scm,hazard)
    let minimalCutSets = ltlDcca.checkWithPromela ()
    do printfn "%+A" minimalCutSets

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