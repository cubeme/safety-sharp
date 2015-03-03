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

namespace SafetySharp.Models
open SafetySharp.Models.Scm

module internal ScmRewriterConvertFaults =
    open ScmHelpers
    open ScmRewriterBase
    open SafetySharp.Workflow
    open ScmWorkflow
    
    
                                        
    type ScmRewriterConvertFaultsState = {
        Model : ScmModel;
        PathOfChangingSubcomponent : CompPath; //path of the Parent of the subcomponent, which gets changed
        TakenNames : Set<string>;

        // Forwarder
        ArtificialFaultOldToFieldNew : Map<Fault,Field>;
        ArtificialFaultOldToPortNew : Map<Fault,ProvPort*ReqPort>;
        BehaviorsToRewrite : BehaviorWithLocation list;
    }
        with
            interface IScmModel<ScmRewriterConvertFaultsState> with
                member this.getModel : ScmModel = this.Model
                member this.setModel (model:ScmModel) =
                    { this with
                        ScmRewriterConvertFaultsState.Model = model
                    }
            interface IScmChangeSubcomponent<ScmRewriterConvertFaultsState> with
                member this.getPathOfChangingSubcomponent = this.PathOfChangingSubcomponent
                member this.setPathOfChangingSubcomponent (compPath:CompPath) =
                    { this with
                        ScmRewriterConvertFaultsState.PathOfChangingSubcomponent = compPath
                    }
            interface IFreshNameDepot<ScmRewriterConvertFaultsState> with
                member this.getTakenNames : Set<string> = this.TakenNames
                member this.setTakenNames (takenNames:Set<string>) =
                    { this with
                        ScmRewriterConvertFaultsState.TakenNames = takenNames
                    }


    type ScmRewriterConvertFaultsFunction<'returnType> = WorkflowFunction<ScmRewriterConvertFaultsState,ScmRewriterConvertFaultsState,'returnType>
    type ScmRewriterConvertFaultsWorkflowState = WorkflowState<ScmRewriterConvertFaultsState>
    

    
    let getConvertFaultsState : ScmRewriterConvertFaultsFunction<ScmRewriterConvertFaultsState> = 
        getState

    let updateConvertFaultsState (newConvertFaults:ScmRewriterConvertFaultsState) : ScmRewriterConvertFaultsFunction<unit> = 
        updateState newConvertFaults




    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Converting Faults
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    

    
    let replaceFaultByPortsAndFields : ScmRewriterConvertFaultsFunction<unit> = workflow {
        let! convertFaultsState = getConvertFaultsState
        let! compDecl = getSubComponentToChange
        if compDecl.Faults = [] then
            return ()
        else
            let faultToConvert = compDecl.Faults.Head

            let! reqPort = getUnusedReqPortName  (sprintf "fault_%s_req" faultToConvert.getName)
            let! provPort = getUnusedProvPortName (sprintf "fault_%s_prov" faultToConvert.getName)
            let! field = getUnusedFieldName (sprintf "fault_%s" faultToConvert.getName)
                            
            let convertedBehavior =
                { faultToConvert.Step with
                    BehaviorDecl.Body = rewriteStm_assignFaultToAssignField (faultToConvert.Fault,field) faultToConvert.Step.Body;
                }

            let newFieldDecl =
                {
                    FieldDecl.Field = field;
                    FieldDecl.Type = Type.BoolType;
                    FieldDecl.Init = [Val.BoolVal(false)] ; //TODO: semantics: a failure is always initially false
                }
            let newReqPortDecl = 
                {
                    ReqPortDecl.ReqPort = reqPort;
                    ReqPortDecl.Params = [];
                }                    
            let newProvPortDecl =
                {
                    ProvPortDecl.FaultExpr = None;
                    ProvPortDecl.ProvPort = provPort;
                    ProvPortDecl.Params = [];
                    ProvPortDecl.Behavior = convertedBehavior;
                    Contract = Scm.Contract.None 
                }
            let newBindingDecl = 
                {
                    BndDecl.Target = {BndTarget.Comp = [compDecl.Comp]; BndTarget.ReqPort = reqPort};
                    BndDecl.Source = {BndSrc.Comp = [compDecl.Comp]; BndSrc.ProvPort = provPort};
                    BndDecl.Kind = BndKind.Instantaneous;
                }                                
            let newCompDecl = compDecl.addField(newFieldDecl)
                                        .addReqPort(newReqPortDecl)
                                        .addProvPort(newProvPortDecl)
                                        .addBinding(newBindingDecl)
                                        .removeFault(faultToConvert) 
            do! updateSubComponentToChange newCompDecl           
            let! convertFaultsState = getConvertFaultsState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
            let newConvertFaultsState =
                { convertFaultsState with
                    ScmRewriterConvertFaultsState.ArtificialFaultOldToFieldNew = convertFaultsState.ArtificialFaultOldToFieldNew.Add ( (faultToConvert.Fault,field) ) ;
                    ScmRewriterConvertFaultsState.ArtificialFaultOldToPortNew = convertFaultsState.ArtificialFaultOldToPortNew.Add ( (faultToConvert.Fault,(newProvPortDecl.ProvPort,newReqPortDecl.ReqPort)) );
                }
            do! updateConvertFaultsState newConvertFaultsState
    }

    let replaceStepFaultByCallPort : ScmRewriterConvertFaultsFunction<unit> = workflow {
        let! convertFaultsState = getConvertFaultsState

        if convertFaultsState.BehaviorsToRewrite.IsEmpty then
            // do not modify old tainted state here
            return ()
        else
            let! compDecl = getSubComponentToChange
            let behaviorToRewriteWithLocation = convertFaultsState.BehaviorsToRewrite.Head
            let behaviorToRewrite = behaviorToRewriteWithLocation.Behavior

            let newBehavior =
                { behaviorToRewrite with
                    BehaviorDecl.Body = rewriteStm_stepFaultToPortCall convertFaultsState.ArtificialFaultOldToPortNew behaviorToRewrite.Body;
                }

            match behaviorToRewriteWithLocation with
                | BehaviorWithLocation.InProvPort (_,provPort,_) ->
                    let newProvPort =
                        { provPort with
                            ProvPortDecl.Behavior = newBehavior;
                        }
                    let newCompDecl = compDecl.replaceProvPort(provPort,newProvPort);
                    do! updateSubComponentToChange newCompDecl
                    let! convertFaultsState = getConvertFaultsState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let newConvertFaultsState =
                        { convertFaultsState with
                            ScmRewriterConvertFaultsState.BehaviorsToRewrite = convertFaultsState.BehaviorsToRewrite.Tail;
                        }
                    do! updateConvertFaultsState newConvertFaultsState
                | BehaviorWithLocation.InFault (_,fault,_) ->
                    let newFault =
                        { fault with
                            FaultDecl.Step = newBehavior;
                        }
                    let newCompDecl = compDecl.replaceFault(fault,newFault);                        
                    do! updateSubComponentToChange newCompDecl
                    let! convertFaultsState = getConvertFaultsState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let newConvertFaultsState =
                        { convertFaultsState with
                            ScmRewriterConvertFaultsState.BehaviorsToRewrite = convertFaultsState.BehaviorsToRewrite.Tail;
                        }
                    do! updateConvertFaultsState newConvertFaultsState
                | BehaviorWithLocation.InStep (_,step,_) ->
                    let newStep =
                        { step with
                            StepDecl.Behavior = newBehavior;
                        }
                    let newCompDecl = compDecl.replaceStep(step,newStep);                        
                    do! updateSubComponentToChange newCompDecl
                    let! convertFaultsState = getConvertFaultsState // To get the updated state. TODO: Make updates to state only by accessor-functions. Then remove this.
                    let newConvertFaultsState =
                        { convertFaultsState with
                            ScmRewriterConvertFaultsState.BehaviorsToRewrite = convertFaultsState.BehaviorsToRewrite.Tail;
                        }
                    do! updateConvertFaultsState newConvertFaultsState
    }

    

    let uniteProvPortDecls  : ScmRewriterConvertFaultsFunction<unit> = workflow {
        //for each ProvPort: replace all ProvPortDecls with the same ProvPort with one ProvPortDecl: Make a guarded command, which differentiates between the different faults
        
        let! convertFaultsState = getConvertFaultsState
        let! compDecl = getSubComponentToChange

        // TODO: Assume semantics:
        //     - For every ProvPort, _exactly_ 1 ProvPortDecl without FaultExpr exists
            
        let provPortDecls = compDecl.ProvPorts

        let provPortToUniteCandidates =
            provPortDecls |> List.filter (fun provPortDecl -> provPortDecl.FaultExpr <> None)
            
        if provPortToUniteCandidates.IsEmpty then
            return ()
        else
            let provPortToUnite =
                // Take the first Candidate
                provPortToUniteCandidates.Head.ProvPort
            let provPortDeclsToUnite =
                provPortDecls |> List.filter (fun provPortDecl -> provPortDecl.ProvPort = provPortToUnite)
            let provPortDeclWithNominalBehavior =
                let provPortDecl =
                    provPortDeclsToUnite |> List.filter (fun provPortDecl -> provPortDecl.FaultExpr = None)
                provPortDecl.Head //must exist, see assumption
            let provPortDeclsWithErrorBehavior =
                provPortDeclsToUnite |> List.filter (fun provPortDecl -> provPortDecl.FaultExpr <> None)
            let unitedVars =
                provPortDeclsToUnite |> List.collect (fun provPortDecl -> provPortDecl.Behavior.Locals)
                                        |> Set.ofList //to remove double entries
                                        |> Set.toList
            let guardStmTuplesOfErrorBehaviors =
                provPortDeclsWithErrorBehavior
                    |> List.map (fun provPortDecl ->
                                    let faultExprAsExpr =
                                        provPortDecl.FaultExpr.Value.rewrite_toExpr convertFaultsState.ArtificialFaultOldToFieldNew
                                    (faultExprAsExpr,provPortDecl.Behavior.Body)
                                )
            let guardStmTupleOfNominalBehavior =
                let elseGuard =
                    let (errorBehaviorGuards,_) = guardStmTuplesOfErrorBehaviors |> List.unzip
                    let oredErrorBehaviorGuards = Expr.createOredExpr errorBehaviorGuards
                    Expr.UExpr(oredErrorBehaviorGuards,UOp.Not)
                (elseGuard,provPortDeclWithNominalBehavior.Behavior.Body)
                
            let guardedCommand =
                Stm.Choice(guardStmTupleOfNominalBehavior::guardStmTuplesOfErrorBehaviors)                
            let newBehavior =
                {
                    BehaviorDecl.Locals = unitedVars;
                    BehaviorDecl.Body = guardedCommand;
                }
            let newProvPort =
                { provPortDeclWithNominalBehavior with
                    ProvPortDecl.Behavior = newBehavior;
                }
            let newCompDecl =
                compDecl.removeProvPorts(provPortDeclsToUnite)
                        .addProvPort(newProvPort)
            do! updateSubComponentToChange newCompDecl
    }    
    
    let uniteStep : ScmRewriterConvertFaultsFunction<unit> = workflow {
          //for each StepDecl: replace all StepDecls one StepDecl: Make a guarded command, which differentiates between the different faults
        let! convertFaultsState = getConvertFaultsState
        let! compDecl = getSubComponentToChange
            
        // TODO: Assume semantics:
        //     - _exactly_ 1 Step without FaultExpr exists
        let needToUnite =
            if compDecl.Steps.Length > 1 then
                true
            else if compDecl.Steps.Length = 0 then
                failwith "BUG: CompDecl needs at least one step"
            else
                false
        if (needToUnite=false) then
            // nothing to do
            return ()
        else
            // now almost 1:1 copy of uniteProvPortDecls
            let stepDecls = compDecl.Steps
            let stepDeclWithNominalBehavior =
                let stepDecl =
                    stepDecls |> List.filter (fun stepDecl -> stepDecl.FaultExpr = None)
                stepDecl.Head //must exist, see assumption
            let stepDeclsWithErrorBehavior =
                stepDecls |> List.filter (fun stepDecl -> stepDecl.FaultExpr <> None)
            let unitedVars =
                stepDecls |> List.collect (fun stepDecl -> stepDecl.Behavior.Locals)
                            |> Set.ofList //to remove double entries
                            |> Set.toList
            let guardStmTuplesOfErrorBehaviors =
                stepDeclsWithErrorBehavior
                    |> List.map (fun stepDecl ->
                                    let faultExprAsExpr =
                                        stepDecl.FaultExpr.Value.rewrite_toExpr convertFaultsState.ArtificialFaultOldToFieldNew
                                    (faultExprAsExpr,stepDecl.Behavior.Body)
                                )
            let guardStmTupleOfNominalBehavior =
                let elseGuard =
                    let (errorBehaviorGuards,_) = guardStmTuplesOfErrorBehaviors |> List.unzip
                    let oredErrorBehaviorGuards = Expr.createOredExpr errorBehaviorGuards
                    Expr.UExpr(oredErrorBehaviorGuards,UOp.Not)
                (elseGuard,stepDeclWithNominalBehavior.Behavior.Body)
                
            let guardedCommand =
                Stm.Choice(guardStmTupleOfNominalBehavior::guardStmTuplesOfErrorBehaviors)                
            let newBehavior =
                {
                    BehaviorDecl.Locals = unitedVars;
                    BehaviorDecl.Body = guardedCommand;
                }
            let newStep =
                { stepDeclWithNominalBehavior with
                    StepDecl.Behavior = newBehavior;
                }
            let newCompDecl =
                compDecl.removeSteps(stepDecls)
                        .addStep(newStep)
                
            do! updateSubComponentToChange newCompDecl
    }
    
    let convertFaults : ScmRewriterConvertFaultsFunction<unit> = workflow {
        do! (iterateToFixpoint replaceFaultByPortsAndFields)
        do! (iterateToFixpoint replaceStepFaultByCallPort)
        do! (iterateToFixpoint uniteProvPortDecls)
        do! uniteStep
    }
       
    let createConvertFaultsStateForRootComponent (model:ScmModel) = 
            let rootComp = model
            let rootPath = [model.Comp]
            let convertFaultsState =
                let behaviorsToRewrite =
                    BehaviorWithLocation.collectAllBehaviorsInPath rootComp rootPath
                {
                    ScmRewriterConvertFaultsState.Model = model;
                    ScmRewriterConvertFaultsState.TakenNames = model.getTakenNames () |> Set.ofList ;
                    ScmRewriterConvertFaultsState.PathOfChangingSubcomponent = rootPath;
                    ScmRewriterConvertFaultsState.ArtificialFaultOldToFieldNew = Map.empty<Fault,Field>;
                    ScmRewriterConvertFaultsState.ArtificialFaultOldToPortNew = Map.empty<Fault,ProvPort*ReqPort>;
                    ScmRewriterConvertFaultsState.BehaviorsToRewrite = behaviorsToRewrite;
                }
            convertFaultsState
            
    
    let convertFaultsWrapper<'oldState when 'oldState :> IScmModel<'oldState>> :
                        WorkflowFunction<'oldState,ScmRewriterConvertFaultsState,unit> = workflow {
        let! model = getModel
        do! updateState (createConvertFaultsStateForRootComponent model)
        do! convertFaults
    }
