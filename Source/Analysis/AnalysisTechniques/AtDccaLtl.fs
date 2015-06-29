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


module internal AtDccaLtl =
    open SafetySharp.Workflow
    open SafetySharp.Models
    open SafetySharp.ITracing
    open SafetySharp.Analysis.Modelchecking.PromelaSpin.Typedefs
    open SafetySharp.Analysis.Modelchecking.PromelaSpin
    open SafetySharp.Models.ScmHelpers
    
    type ElementToCheck = {
        FaultsWhichMayAppear:Set<FaultPath>; //faultyComponents
        FaultsWhichMustNotAppear:Set<FaultPath>;
        CorrespondingFormula : ScmVerificationElements.LtlExpr;
    }

    type PerformDccaWithLtlFormulas (untransformedModel:Scm.ScmModel,hazard:ScmVerificationElements.PropositionalExpr) =
        
        let mutable cachedPromelaModel = Map.empty<Scm.ScmModel,SamToPromela.PromelaTracer<Scm.Traceable>>

        
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
        let transformModelToPromelaAndCache_asSubWorkflow () = runSubWorkflow_WithSameState_ReturnState (transformModelToPromelaAndCache ())

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
            let! promelaTracer = transformModelToPromelaAndCache_asSubWorkflow()

            let checkFormulaElement (formulaElement:ElementToCheck) = workflow {                    
                    let promelaModelWithFormula = 
                        { promelaTracer.PrSpec with
                            PrSpec.Formulas = [SafetySharp.Analysis.Modelchecking.PromelaSpin.ScmVeToPromela.transformLtlExpression promelaTracer.ForwardTracer (formulaElement.CorrespondingFormula)] 
                        }
                    do! updateState promelaModelWithFormula
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
            
        /////////////////////////////////////////////////
        //              NuSMV-Code
        /////////////////////////////////////////////////
        member this.checkWithNusmv ()  : WorkflowFunction<Scm.ScmModel,Scm.ScmModel,Set<Set<FaultPath>>> = workflow {
            let nusmvExecutor = new SafetySharp.ExternalTools.Smv.ExecuteNusmv2()
            
            let transformModelToNuSMV = workflow {                    
                    do! SafetySharp.Models.ScmTracer.scmToSimpleScmTracer ()
                    do! SafetySharp.ExternalTools.ScmToNuXmv.transformConfiguration ()
                    do! logForwardTracesOfOrigins ()
                    let! forwardTracer = getForwardTracer ()
                    let! nusmvModel = getState ()
                    do! SafetySharp.ITracing.removeTracing ()
                    do! SafetySharp.ExternalTools.SmvToString.workflow ()
                    let! file = printToRandomFile "smv"
                    let filename = match file with | SafetySharp.FileSystem.FileName(filename) -> filename
                    do nusmvExecutor.StartSmvInteractive (0) (filename+".log") |> ignore
                    let readmodel = nusmvExecutor.ExecuteAndIntepretCommandSequence(SafetySharp.ExternalTools.Smv.SmvHelpfulCommandsAndCommandSequences.readModelAndBuildBdd filename)
                    assert readmodel.HasSucceeded
                    return (nusmvModel,forwardTracer)
            }
            let! (nusmvModel,forwardTracer) = runSubWorkflow_WithSameState_ReturnResult transformModelToNuSMV            
            //    let threadWithBiggerStack = new System.Threading.Thread( (fun () -> result := ltlDcca.checkWithNuSMV () ), 1024*1024*8) //HACK: for a bigger stack
            //    do threadWithBiggerStack.Start ()
            //    do threadWithBiggerStack.Join ()


            let checkFormulaElement (formulaElement:ElementToCheck) =
                    let nusmvLtl = SafetySharp.ExternalTools.ScmVeToNuXmv.transformLtlExpression forwardTracer formulaElement.CorrespondingFormula
                    let nuXmvResult = nusmvExecutor.ExecuteCommand(SafetySharp.ExternalTools.Smv.NuSMVCommand.CheckLtlSpec nusmvLtl)
                    let nuXmvInterpretation = SafetySharp.ExternalTools.Smv.SmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec nuXmvResult
                    (formulaElement.FaultsWhichMayAppear,nuXmvInterpretation)

            let checkIfSizeIsSafe (knownUnsafe:Set<Set<FaultPath>>) (size:int) : Set<Set<FaultPath>> = //returns new knownUnsafe
                let formulasToCheck = this.formulasToVerify_CheckIfNumberOfFaultsIsSafe size knownUnsafe
                let checkedFormulas =
                    formulasToCheck |> List.map (fun formula -> checkFormulaElement formula)
                let calculateNewKnownUnsafe (acc:Set<Set<FaultPath>>) (toProcess:(Set<FaultPath>*SafetySharp.ExternalTools.Smv.NuXmvCommandResultInterpretedCheckOfSpecification)) =
                    let faultyComponents,result = toProcess
                    match result.Result with
                        | SafetySharp.ExternalTools.Smv.CheckOfSpecificationDetailedResult.Invalid (trace)->
                            acc.Add faultyComponents // model checker finds counterexample. Formula is false. Combination is unsafe.
                        | SafetySharp.ExternalTools.Smv.CheckOfSpecificationDetailedResult.Valid ->
                            acc // model checker finds no counterexample. Formula is true. Combination is safe.
                        | SafetySharp.ExternalTools.Smv.CheckOfSpecificationDetailedResult.Undetermined ->
                            printfn "stdout: %s\n stderr: %s" (result.Basic.Stdout) (result.Basic.Stderr)
                            failwith "Could not be checked with NuSMV. Consult full log"
                checkedFormulas |> List.fold calculateNewKnownUnsafe knownUnsafe
            
            let fullDcca : Set<Set<FaultPath>> =
                {0..numberOfAllFaults} |> Seq.toList |> List.fold checkIfSizeIsSafe (Set.empty<Set<FaultPath>>)
            do nusmvExecutor.ForceShutdownSmv () 
            return fullDcca
        }