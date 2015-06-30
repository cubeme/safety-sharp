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

module internal AtDccaPruning =
    open SafetySharp.Workflow

    
    open SafetySharp.Workflow
    open SafetySharp.Models
    open SafetySharp.ITracing
    open SafetySharp.Analysis.Modelchecking.PromelaSpin.Typedefs
    open SafetySharp.Analysis.Modelchecking.PromelaSpin
    open SafetySharp.Models.ScmHelpers
    
    type ElementToCheck = {
        FaultsWhichMayAppear:Set<FaultPath>; //faultyComponents
        FaultsWhichMustNotAppear:Set<FaultPath>;
    }

    type PerformDccaByPruningModels (untransformedModel:Scm.ScmModel,hazard:ScmVerificationElements.PropositionalExpr) =
        
        let mutable cachedPromelaModel = Map.empty<Scm.ScmModel,SamToPromela.PromelaTracer<Scm.Traceable>>

        
        let transformModelToPromelaAndCache () : ExogenousWorkflowFunction<ScmTracer.SimpleScmTracer<Scm.Traceable>,SamToPromela.PromelaTracer<Scm.Traceable>> = workflow {
            let! model = ScmTracer.iscmGetModel ()
            if not(cachedPromelaModel.ContainsKey model) then
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmToPromela.transformConfigurationWithInvariants [hazard]
                do! logForwardTracesOfOrigins ()
                let! transformed = getState ()
                cachedPromelaModel <- cachedPromelaModel.Add (model,transformed)
                return ()
            else
                do! updateState (cachedPromelaModel.Item model)
                return ()
        }

        /////////////////////////////////////////////////
        //              COMMON CODE
        /////////////////////////////////////////////////

        //let hazardAsLtl = ScmVerificationElements.LtlExpr.fromPropositionalExpr hazard
        let allFaultsAsList = untransformedModel.getFaults
        let allFaultsAsSet = allFaultsAsList |> Set.ofList
        let numberOfAllFaults = allFaultsAsSet.Count
        // assert (List.Length allFaultsAsList = Set.count allFaultsAsSet)

        member this.``even when these faults appear, system is safe``(faultsWhichMayAppear:Set<FaultPath>) : ElementToCheck =
            let faultsWhichMustNotAppear = Set.difference allFaultsAsSet faultsWhichMayAppear
            {
                FaultsWhichMayAppear = faultsWhichMayAppear;
                FaultsWhichMustNotAppear = faultsWhichMustNotAppear;
            }

        member this.isAlreadyKnownThatUnsafe (knownUnsafe:Set<Set<FaultPath>>) (toCheck:Set<FaultPath>) : bool =
            let doesSetShowThatUnsafe (unsafeSet:Set<FaultPath>) =
                Set.isSubset unsafeSet toCheck
            knownUnsafe |> Set.exists doesSetShowThatUnsafe

        
        member this.formulasToVerify_CheckIfNumberOfFaultsIsSafe (exactNumberOfFaults:int) (knownUnsafe:Set<Set<FaultPath>>) : ElementToCheck list =
            // we assume, that we increase the number of faults each step (the other direction is also possible and may be advantageous in several cases)
            // formulasToVerify_CheckIfNumberOfFaultsIsSafe (0) ...
            // formulasToVerify_CheckIfNumberOfFaultsIsSafe (...) ...
            // formulasToVerify_CheckIfNumberOfFaultsIsSafe (allFaults.Size) ...
            let rec createCandidates (selectionsLeft:int,decisionsLeft:int) (alreadyInSet:Set<FaultPath>) (toDecide:FaultPath list) : Set<FaultPath> list =
                if selectionsLeft <= 0 then
                    [alreadyInSet]
                else if decisionsLeft = selectionsLeft then                    
                    let takeTheRest = toDecide |> Set.ofList |> Set.union alreadyInSet
                    [takeTheRest]
                else
                    assert (toDecide.IsEmpty = false)
                    let selectedBranch =    createCandidates (selectionsLeft - 1, decisionsLeft - 1) (alreadyInSet.Add (toDecide.Head)) (toDecide.Tail)
                    let notSelectedBranch = createCandidates (selectionsLeft,     decisionsLeft - 1) (alreadyInSet)                     (toDecide.Tail)
                    selectedBranch@notSelectedBranch
            let allCandidates = createCandidates (exactNumberOfFaults,numberOfAllFaults) (Set.empty<FaultPath>) (allFaultsAsList)
            let filteredCandidates = allCandidates |> List.filter (fun candidate -> not (this.isAlreadyKnownThatUnsafe knownUnsafe candidate))
            let ltlOfFilteredCandidates = filteredCandidates |> List.map this.``even when these faults appear, system is safe``
            ltlOfFilteredCandidates
            
        /////////////////////////////////////////////////
        //              PROMELA/SPIN CODE
        /////////////////////////////////////////////////
        
        member this.checkWithPromela () : WorkflowFunction<Scm.ScmModel,Scm.ScmModel,Set<Set<FaultPath>>> = workflow {
            let checkFormulaElement (formulaElement:ElementToCheck) = workflow {                    
                    do! SafetySharp.Models.ScmTracer.scmToSimpleScmTracer ()
                    do! SafetySharp.Models.ScmRewriterRemoveGivenFaults.removeFaults formulaElement.FaultsWhichMustNotAppear
                    let! promelaTracer = transformModelToPromelaAndCache ()
                    do! removeTracing ()
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPanOnModel ()
                    do! printToLog ()
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.interpretWorkflow ()
                    let! panIntepretation = getState ()
                    return (formulaElement.FaultsWhichMayAppear,panIntepretation)
            }
            let checkFormulaElement_asSubWorkflow element = runSubWorkflow_WithSameState_ReturnResult (checkFormulaElement element)

            let checkIfSizeIsSafe (knownUnsafe:Set<Set<FaultPath>>) (size:int) : WorkflowFunction<Scm.ScmModel,Scm.ScmModel,Set<Set<FaultPath>>> = workflow {
                let formulasToCheck = this.formulasToVerify_CheckIfNumberOfFaultsIsSafe size knownUnsafe
                let! checkedFormulas = listMap checkFormulaElement_asSubWorkflow formulasToCheck
                let checkedFormulasSet = checkedFormulas |> Set.ofList

                let calculateNewKnownUnsafe (acc:Set<Set<FaultPath>>) (toProcess:(Set<FaultPath>*SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationLog)) =
                    let faultyComponents,result = toProcess
                    match result.Result with
                        | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.False ->
                            acc.Add faultyComponents // model checker finds counterexample. Formula is false. Combination is unsafe.
                        | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.True ->
                            acc // model checker finds no counterexample. Formula is true. Combination is safe.
                        | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.Maybe ->
                            printf "%s" result.FullLog
                            failwith "Could not be checked with Spin. Possible reason: Search depth too small. Consult full log"
                let unsafeSetsUntilSize = checkedFormulasSet |> Set.fold calculateNewKnownUnsafe knownUnsafe
                return unsafeSetsUntilSize
            }
            
            let sizesToCheck = {0..numberOfAllFaults} |> Seq.toList
            let! fullDcca = listFold checkIfSizeIsSafe (Set.empty<Set<FaultPath>>) sizesToCheck
            return fullDcca
        }