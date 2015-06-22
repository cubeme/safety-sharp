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

namespace SafetySharp.Analysis.Techniques

open SafetySharp.EngineOptions

module internal AtDccaLtl =
    open SafetySharp.Workflow
    open SafetySharp.Models
    open SafetySharp.ITracing
    open SafetySharp.Analysis.Modelchecking.PromelaSpin.Typedefs
    open SafetySharp.Models.ScmHelpers
    
    type ElementToCheck = {
        FaultsWhichMayAppear:Set<FaultPath>; //faultyComponents
        FaultsWhichMustNotAppear:Set<FaultPath>;
        CorrespondingFormula : ScmVerificationElements.LtlExpr;
    }

    type PerformDccaWithLtlFormulas (untransformedModel:Scm.ScmModel,hazard:ScmVerificationElements.PropositionalExpr) =
        

        /////////////////////////////////////////////////
        //              COMMON CODE
        /////////////////////////////////////////////////

        let hazardAsLtl = ScmVerificationElements.LtlExpr.fromPropositionalExpr hazard
        let allFaultsAsList = untransformedModel.getFaults
        let allFaultsAsSet = allFaultsAsList |> Set.ofList
        let numberOfAllFaults = allFaultsAsSet.Count
        // assert (List.Length allFaultsAsList = Set.count allFaultsAsSet)

        member this.``even when these faults appear, system is safe``(faultsWhichMayAppear:Set<FaultPath>) : ElementToCheck =
            let faultsWhichMustNotAppear = Set.difference allFaultsAsSet faultsWhichMayAppear
            let faultsWhichMustNotAppearLtl =
                faultsWhichMustNotAppear
                    |> Set.toList
                    |> List.map (fun fault -> ScmVerificationElements.LtlExpr.UExpr(ScmVerificationElements.LtlExpr.ReadFault(fault),Scm.UOp.Not))
                    |> ScmVerificationElements.LtlExpr.createAndedExpr
            let correspondingFormula = ScmVerificationElements.LtlExpr.UExpr(ScmVerificationElements.LtlExpr.LbExpr(faultsWhichMustNotAppearLtl,ScmVerificationElements.LbOp.Until,hazardAsLtl),Scm.UOp.Not)
            {
                FaultsWhichMayAppear = faultsWhichMayAppear;
                FaultsWhichMustNotAppear = faultsWhichMustNotAppear;
                CorrespondingFormula = correspondingFormula;
            }

        member this.isAlreadyKnownThatUnsafe (knownUnsafe:Set<FaultPath> list) (toCheck:Set<FaultPath>) : bool =
            let doesSetShowThatUnsafe (unsafeSet:Set<FaultPath>) =
                Set.isSubset unsafeSet toCheck
            knownUnsafe |> List.exists doesSetShowThatUnsafe

        
        member this.formulasToVerify_CheckIfNumberOfFaultsIsSafe (exactNumberOfFaults:int) (knownUnsafe:Set<FaultPath> list) : ElementToCheck list =
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
        member this.checkWithPromela () =
            let transformModelToPromela = workflow {
                    do! SafetySharp.Models.ScmMutable.setInitialPlainModelState untransformedModel
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmToPromela.transformConfiguration ()
                    do! logForwardTracesOfOrigins ()
                    let! forwardTracer = getForwardTracer ()
                    let! promelaModel = getState ()
                    return (promelaModel,forwardTracer)
            }
            let ((promelaModel,forwardTracer),wfStateWithPromelaModel) = runWorkflow_getResultAndWfState transformModelToPromela            
            
            let checkFormulaElement (formulaElement:ElementToCheck) = workflow {                    
                    let promelaModelWithFormula = 
                        { promelaModel.PrSpec with
                            PrSpec.Formulas = [SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmVeToPromela.transformLtlExpression forwardTracer (formulaElement.CorrespondingFormula)] 
                        }
                    do! updateState promelaModelWithFormula
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPanOnModel ()
                    do! printToStdout ()
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.interpretWorkflow ()
                    let! panIntepretation = getState ()
                    return (formulaElement.FaultsWhichMayAppear,panIntepretation)
            }

            let checkIfSizeIsSafe (knownUnsafe:Set<FaultPath> list) (size:int) : Set<FaultPath> list = //returns new knownUnsafe
                let formulasToCheck = this.formulasToVerify_CheckIfNumberOfFaultsIsSafe size knownUnsafe
                let checkedFormulas =
                    formulasToCheck |> List.map (fun formula -> runWorkflowState_getResult (checkFormulaElement formula) wfStateWithPromelaModel)
                let calculateNewKnownUnsafe (acc:Set<FaultPath> list) (toProcess:(Set<FaultPath>*SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationLog)) =
                    let faultyComponents,result = toProcess
                    match result.Result with
                        | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.False ->
                            faultyComponents::acc // model checker finds counterexample. Formula is false. Combination is unsafe.
                        | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.True ->
                            acc // model checker finds no counterexample. Formula is true. Combination is safe.
                        | SafetySharp.Analysis.Modelchecking.PromelaSpin.PanInterpretResult.PanVerificationResult.Maybe ->
                            printf "%s" result.FullLog
                            failwith "Could not be checked with Spin. Possible reason: Search depth too small. Consult full log"
                checkedFormulas |> List.fold calculateNewKnownUnsafe knownUnsafe
            
            let fullDcca : Set<FaultPath> list =
                {0..numberOfAllFaults} |> Seq.toList |> List.fold checkIfSizeIsSafe ([]:Set<FaultPath> list)
            fullDcca

            
        /////////////////////////////////////////////////
        //              NuXmv-Code
        /////////////////////////////////////////////////
        member this.checkWithNuXmv () =            
            let nuxmvExecutor = new SafetySharp.ExternalTools.Smv.ExecuteNuXmv()
            
            let transformModelToNuXmv = workflow {
                    do! setEngineOption(TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep)

                    do! SafetySharp.Models.ScmMutable.setInitialPlainModelState untransformedModel
                    do! SafetySharp.ExternalTools.ScmToNuXmv.transformConfiguration ()
                    do! logForwardTracesOfOrigins ()
                    let! forwardTracer = getForwardTracer ()
                    let! nuxmvModel = getState ()
                    do! SafetySharp.ITracing.removeTracing ()
                    do! SafetySharp.ExternalTools.SmvToString.workflow ()
                    let filename = "verification.smv" |> SafetySharp.FileSystem.FileName
                    do! saveToFile filename
                    do nuxmvExecutor.StartNuXmvInteractive (0) ("verification.smv.log") |> ignore
                    let readmodel = nuxmvExecutor.ExecuteAndIntepretCommandSequence(SafetySharp.ExternalTools.Smv.NuXmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd "verification.smv")
                    assert readmodel.HasSucceeded
                    return (nuxmvModel,forwardTracer)
            }
            let ((nuxmvModel,forwardTracer),wfStateWithNuxmvModel) = runWorkflow_getResultAndWfState transformModelToNuXmv            
            

            let checkFormulaElement (formulaElement:ElementToCheck) =
                    let nuxmvLtl = SafetySharp.ExternalTools.ScmVeToNuXmv.transformLtlExpression forwardTracer formulaElement.CorrespondingFormula
                    let nuXmvResult = nuxmvExecutor.ExecuteCommand(SafetySharp.ExternalTools.Smv.NuSMVCommand.CheckLtlSpec nuxmvLtl)
                    let nuXmvInterpretation = SafetySharp.ExternalTools.Smv.NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec nuXmvResult
                    (formulaElement.FaultsWhichMayAppear,nuXmvInterpretation)

            let checkIfSizeIsSafe (knownUnsafe:Set<FaultPath> list) (size:int) : Set<FaultPath> list = //returns new knownUnsafe
                let formulasToCheck = this.formulasToVerify_CheckIfNumberOfFaultsIsSafe size knownUnsafe
                let checkedFormulas =
                    formulasToCheck |> List.map (fun formula -> checkFormulaElement formula)
                let calculateNewKnownUnsafe (acc:Set<FaultPath> list) (toProcess:(Set<FaultPath>*SafetySharp.ExternalTools.Smv.NuXmvCommandResultInterpretedCheckOfSpecification)) =
                    let faultyComponents,result = toProcess
                    match result.Result with
                        | SafetySharp.ExternalTools.Smv.CheckOfSpecificationDetailedResult.Invalid (trace)->
                            faultyComponents::acc // model checker finds counterexample. Formula is false. Combination is unsafe.
                        | SafetySharp.ExternalTools.Smv.CheckOfSpecificationDetailedResult.Valid ->
                            acc // model checker finds no counterexample. Formula is true. Combination is safe.
                        | SafetySharp.ExternalTools.Smv.CheckOfSpecificationDetailedResult.Undetermined ->
                            printfn "stdout: %s\n stderr: %s" (result.Basic.Stdout) (result.Basic.Stderr)
                            failwith "Could not be checked with Spin. Possible reason: Search depth too small. Consult full log"
                checkedFormulas |> List.fold calculateNewKnownUnsafe knownUnsafe
            
            let fullDcca : Set<FaultPath> list =
                {0..numberOfAllFaults} |> Seq.toList |> List.fold checkIfSizeIsSafe ([]:Set<FaultPath> list)
            do nuxmvExecutor.ForceShutdownNuXmv () 
            fullDcca