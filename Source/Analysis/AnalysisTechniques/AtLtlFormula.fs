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

namespace SafetySharp.AnalysisTechniques

module internal AtLtlFormula =
    open SafetySharp.Workflow
    open SafetySharp.Models
    open SafetySharp.ITracing
    open SafetySharp.Analysis.Modelchecking.PromelaSpin.Typedefs

    type AnalyseLtlFormulas (untransformedModel:Scm.ScmModel) =
    
        //let mutable formulasToVerify : ScmVerificationElements.LtlExpr list = []
        //member this.checkLtlFormulaLazy (formula: ScmVerificationElements.LtlExpr) =
            // TODO: Implementation
            // Some engines (e.g. PromelaSpin) work most efficiently if formulas are evaluated in sequence other
            // engines (e.g. NuSMV on CTL, Prism) work most efficiently if they can evaluate a bunch of formulas at the same time.
            // This function allows to collect several formulas before evaluating them. It only ensures that
            // when a _result_ of a formula is _accessed_ this formula will be calculated. Depending on the engine
            // other formulas may be calculated in the same bunch.
          //  formulasToVerify <- formula :: formulasToVerify

        member this.checkLtlFormula (formula: ScmVerificationElements.LtlExpr) =
            ()

        member this.checkWithPromela () =        
            let transformModelToPromela = workflow {
                    do! SafetySharp.Models.ScmTracer.setInitialPlainModelState untransformedModel
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmToPromela.transformConfiguration ()
                    do! logForwardTracesOfOrigins ()
                    let! forwardTracer = getForwardTracer ()
                    let! promelaModel = getState ()
                    return (promelaModel,forwardTracer)
            }
            let ((promelaModel,forwardTracer),wfState) = runWorkflow_getResultAndWfState transformModelToPromela            
            let promelaModelWithFormulas = 
                { promelaModel.PrSpec with
                    PrSpec.Formulas = formulasToVerify |> List.map (SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmVeToPromela.transformLtlExpression forwardTracer)
                }
            let executeModelWithFormulas = workflow {
                do! updateState promelaModelWithFormulas
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPanOnModel ()
                do! printToStdout ()
            }
            let (_,wfState) = runWorkflowState executeModelWithFormulas wfState //must continue with resulting wfState to keep the tracing
            ()