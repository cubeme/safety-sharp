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
    open SafetySharp.Analysis.Modelchecking.PromelaSpin
    open SafetySharp.Ternary

    type AnalyseLtlFormulas () =
    
        let mutable cachedPromelaModel = Map.empty<Scm.ScmModel,SamToPromela.PromelaTracer<Scm.Traceable>>
    
        //let mutable formulasToVerify : ScmVerificationElements.LtlExpr list = []
        //member this.checkLtlFormulaLazy (formula: ScmVerificationElements.LtlExpr) =
            // TODO: Implementation
            // Some engines (e.g. PromelaSpin) work most efficiently if formulas are evaluated in sequence other
            // engines (e.g. NuSMV on CTL, Prism) work most efficiently if they can evaluate a bunch of formulas at the same time.
            // This function allows to collect several formulas before evaluating them. It only ensures that
            // when a _result_ of a formula is _accessed_ this formula will be calculated. Depending on the engine
            // other formulas may be calculated in the same bunch.
          //  formulasToVerify <- formula :: formulasToVerify

          
        let transformModelToPromelaAndCache () : ExogenousWorkflowFunction<Scm.ScmModel,SamToPromela.PromelaTracer<Scm.Traceable>> = workflow {
            let! model = getState ()
            if not(cachedPromelaModel.ContainsKey model) then
                do! SafetySharp.Models.ScmTracer.scmToSimpleScmTracer ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmToPromela.transformConfiguration ()
                do! logForwardTracesOfOrigins ()
                let! transformed = getState ()
                cachedPromelaModel <- cachedPromelaModel.Add (model,transformed)
                return ()
            else
                do! updateState (cachedPromelaModel.Item model)
                return ()
        }

        member this.checkLtlFormulaWithPromela (formula: ScmVerificationElements.LtlExpr)
                    : WorkflowFunction<Scm.ScmModel,_,Ternary> = workflow {                    
            do! transformModelToPromelaAndCache ()
            let! promelaTracer = getState ()
            let transformedFormula = SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmVeToPromela.transformLtlExpression promelaTracer.ForwardTracer formula
            let promelaModelWithFormulas = 
                { promelaTracer.PrSpec with
                    Typedefs.PrSpec.Formulas = [transformedFormula];
                }
            do! updateState promelaModelWithFormulas
            do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
            do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPanOnModel ()
            do! printToLog ()
            do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.interpretWorkflow ()
            let! panIntepretation = getState ()
            match panIntepretation.Result with
                | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.False ->
                    return Ternary.False
                | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.True ->
                    return Ternary.True
                | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.Maybe ->
                    return Ternary.Unknown
        }