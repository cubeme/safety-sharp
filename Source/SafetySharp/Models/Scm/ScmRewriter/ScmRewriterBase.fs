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

namespace SafetySharp.Models.Scm

module internal ScmRewriterBase =
    open ScmHelpers

    
    type ScmModel = CompDecl //may change, but I hope it does not
    
    type ScmRewriterLevelUp = {  //TODO: Rename to data, move into file
        // child lives in parent. Things from the child are moved
        // into the parent. The path to the parent is declared in the ScmRewriterState
        NameOfChildToRewrite : Comp;
        
        // Forwarder
        // For each of these. Map goes from:old -> to:new. Old entity lives always in ChildPath, new in ParentPath
        // So no path is necessary
        ArtificialFieldsOldToNew : Map<Field,Field>
        ArtificialFaultsOldToNew : Map<Fault,Fault>
        ArtificialReqPortOldToNew : Map<ReqPort,ReqPort>
        ArtificialProvPortOldToNew : Map<ProvPort,ProvPort>

        //Maps from new path to old path (TODO: when not necessary, delete); or change to newToOrigin
        ArtificialFieldsNewToOld : Map<FieldPath,FieldPath> 
        ArtificialFaultsNewToOld : Map<FaultPath,FaultPath>        
        ArtificialReqPortNewToOld : Map<ReqPortPath,ReqPortPath>
        ArtificialProvPortNewToOld : Map<ProvPortPath,ProvPortPath>
        
        FaultsToRewrite : FaultDecl list    //declared in parent
        ProvPortsToRewrite : ProvPortDecl list    //declared in parent
        StepsToRewrite : StepDecl list    //declared in parent
        ArtificialStep : (ReqPort*ProvPort) option
    }
        with
            member levelUp.oldToNewMaps1 =                
                    (levelUp.ArtificialReqPortOldToNew,levelUp.ArtificialFaultsOldToNew,Map.empty<Var,Var>,levelUp.ArtificialFieldsOldToNew)
            member levelUp.oldToNewMaps2 =                
                    (levelUp.ArtificialFaultsOldToNew)
            //member levelUp.ParentCompDecl =
            //        levelUp.ParentCompDecl
                                        
    type ScmRewriterConvertFaults = { //TODO: Rename to data, move into file
        // Forwarder
        ArtificialFaultOldToFieldNew : Map<Fault,Field>;
        ArtificialFaultOldToPortNew : Map<Fault,ProvPort*ReqPort>;
        BehaviorsToRewrite : BehaviorWithLocation list;
    }
                
    type ScmConvertDelayedBindings = unit
    
    type ScmRewriterInlineBehavior = {
        BehaviorToReplace : BehaviorWithLocation;
        InlinedBehavior : BehaviorDecl;
        CallToReplace : StmPath option;
        (*ArtificialLocalVarOldToNew : Map<VarDecl,VarDecl>;*)
    }
        with
            static member createEmptyFromBehavior (behaviorWithLocaltion:BehaviorWithLocation) =
                {
                    ScmRewriterInlineBehavior.BehaviorToReplace = behaviorWithLocaltion;
                    ScmRewriterInlineBehavior.InlinedBehavior = behaviorWithLocaltion.Behavior;
                    ScmRewriterInlineBehavior.CallToReplace = None;
                }
            
    type ScmRewriteState<'subState> = {
        Model : ScmModel;

        ChangingSubComponent : CompDecl;
        PathOfChangingSubcomponent : CompPath;

        TakenNames : Set<string>;
        SubState : 'subState;
        // TODO: Optimization: Add parent of ComponentToRemove here. Thus, when a change to the componentToRemove is done, only its parent needs to be updated and not the whole model.
        //       The writeBack to the model can happen, when a component gets deleted
        // Flag, which determines, if something was changed (needed for fixpoint iteration)
        LevelUp : ScmRewriterLevelUp option;
        InlineBehavior : ScmRewriterInlineBehavior option;
        ConvertDelayedBindings : ScmConvertDelayedBindings option;
        ConvertFaults : ScmRewriterConvertFaults option;
        Tainted : bool;
    }
        with
            static member initial (scm:ScmModel) (subState:'subState) = 
                {
                    ScmRewriteState.Model = scm;
                    ChangingSubComponent = scm;
                    PathOfChangingSubcomponent = [scm.Comp];
                    ScmRewriteState.TakenNames = scm.getTakenNames () |> Set.ofList;
                    ScmRewriteState.LevelUp = None;
                    ScmRewriteState.SubState = subState;
                    ScmRewriteState.InlineBehavior = None;
                    ScmRewriteState.ConvertDelayedBindings = None;
                    ScmRewriteState.ConvertFaults = None;
                    ScmRewriteState.Tainted = false;
                }
                    
    let initiaScmRewriterStateWithoutSubState (scm:ScmModel) = ScmRewriteState<unit>.initial scm ()

                
    
    // ScmRewriteFunction<'subState,'returnType>, where 'subState is a special state (with interface rewriteInit), where everything like ScmRewriterInlineBehavior is encapsulated. Write converter-functions (every subRewriter should contain a "toUnit", where 'b=unit.
    // RewriteState should also be parametrized. We could also rename scmRewriter to ScmLocalRewriter (it works only on one component(and maybe its subcomponent) 
    type ScmRewriteFunction<'subState,'returnType> = ScmRewriteFunction of (ScmRewriteState<'subState> -> 'returnType * ScmRewriteState<'subState>)
    
    let iterateToFixpoint<'subState> (s:ScmRewriteFunction<'subState,unit>) =
        match s with
            | ScmRewriteFunction (functionToIterate) ->            
                let adjust_tainted_and_call (state:ScmRewriteState<'subState>) : (bool*ScmRewriteState<'subState>) =
                    // 1) Tainted is set to false
                    // 2) function is called
                    // 3) Tainted is set to true, if (at least one option applies)
                    //      a) it was true before the function call
                    //      b) the functionToIterate sets tainted to true 
                    let wasTaintedBefore = state.Tainted
                    let stateButUntainted =
                        { state with
                            ScmRewriteState.Tainted = false;
                        }
                    let (_,stateAfterCall) = functionToIterate stateButUntainted
                    let taintedByCall = stateAfterCall.Tainted
                    let newState =
                        { stateAfterCall with
                            ScmRewriteState.Tainted = wasTaintedBefore || taintedByCall;
                        }
                    (taintedByCall,newState)
                let rec iterate (state:ScmRewriteState<'subState>) : (unit*ScmRewriteState<'subState>) =
                    let (taintedByCall,stateAfterOneCall) = adjust_tainted_and_call state
                    if taintedByCall then
                        iterate stateAfterOneCall
                    else
                        ((),stateAfterOneCall)
                ScmRewriteFunction (iterate)

    // TODO:
    //   - RewriteElement should return, if it made a change
    //   - smallest element only gets called once
    //   - liftToFixpoint repeats a small element, until it doesn't change something anymore
    //   - so levelUpField levels up one field, levelUpFields levels up fields, until nothing possible anymore


    let runState (ScmRewriteFunction s) a = s a
    let getState = ScmRewriteFunction (fun s -> (s,s)) //Called in workflow: (implicitly) gets state (s) from workflow; assign this State s to the let!; and set (in this case keep)State of workflow to s
    let putState s = ScmRewriteFunction (fun _ -> ((),s)) //Called in workflow: ignore state (_) from workflow; assign nothing () to the let!; and set State of workflow to the new state s
    let putStateAndReturn s returnValue = ScmRewriteFunction (fun _ -> (returnValue,s))//Called in workflow: ignore state (_) from workflow; assign returnValue to the let!; and set State of workflow to the new state s

    // the computational expression "scmRewrite" is defined here
    // inspired by http://fsharpforfunandprofit.com/posts/computation-expressions-intro/ (StateBuilder, now offline)
    type ScmRewriter() =
        member this.Return(a) = 
            ScmRewriteFunction (fun s -> (a,s))
        member this.Bind(m,k) =
            ScmRewriteFunction (fun state -> 
                let (a,state') = runState m state 
                runState (k a) state')
        member this.ReturnFrom (m) =
            m

    let scmRewrite = new ScmRewriter()

    
    // helpers
    
    // TODO:
    // let! x = (stateFromLevelUp scmRewriteLevelUp{...})
    // let fromBaseState = ... (execute and write back)
    // let getUnusedFieldName = (fromBaseState ScmRewriterBase.getUnusedFieldName)
    

    let getCompletlyFreshName<'subState> (basedOn:string) : ScmRewriteFunction<'subState,string> = scmRewrite {
            let! state = getState
            let newName = 
                let existsName (nameCandidate:string) : bool =
                    state.TakenNames.Contains nameCandidate
                let rec inventName numberSuffix : string =
                    // If desired name does not exist, get name with the lowest numberSuffix.
                    // This is not really beautiful, but finally leads to a free name, (because domain is finite).
                    let nameCandidate = sprintf "%s_art%i" basedOn numberSuffix
                    if existsName nameCandidate = false then
                        nameCandidate
                    else
                        inventName (numberSuffix+1)
                if existsName basedOn = false then
                    basedOn
                else
                    inventName 0
            let modifiedState =
                { state with
                    ScmRewriteState.TakenNames = state.TakenNames.Add newName;
                    ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                }
            return! putStateAndReturn modifiedState newName
        }

    let getUnusedFieldName<'subState> (basedOn:string) : ScmRewriteFunction<'subState,Field> = scmRewrite {
            let! name = getCompletlyFreshName basedOn
            return Field(name)
        }

    let getUnusedFaultName<'subState> (basedOn:string) : ScmRewriteFunction<'subState,Fault> = scmRewrite {
            let! name = getCompletlyFreshName basedOn
            return Fault.Fault(name)
        }
            
    let getUnusedReqPortName<'subState> (basedOn:string) : ScmRewriteFunction<'subState,ReqPort> = scmRewrite {
            let! name = getCompletlyFreshName basedOn
            return ReqPort(name)
        }

    let getUnusedProvPortName<'subState> (basedOn:string) : ScmRewriteFunction<'subState,ProvPort> = scmRewrite {
            let! name = getCompletlyFreshName basedOn
            return ProvPort(name)
        }
        
    let getUnusedVarName<'subState> (basedOn:string) : ScmRewriteFunction<'subState,Var> = scmRewrite {
            let! name = getCompletlyFreshName basedOn
            return Var(name)
        }

    let getUnusedVarNames<'subState> (basedOn:string list) : ScmRewriteFunction<'subState,Var list> = 
        let newUnusedVarNames (state) : (Var list * ScmRewriteState<'subState>) =
            let mutable varState = state
            let mutable newVars = []
            for i in basedOn do
                let (newVar,newState) = runState (getUnusedVarName i) varState
                varState <- newState
                newVars <- newVar::newVars
            (List.rev newVars, varState)
        ScmRewriteFunction (newUnusedVarNames)

    let getUnusedFieldNames<'subState> (basedOn:string list) : ScmRewriteFunction<'subState,Field list> = 
        let newUnusedFieldNames (state) : (Field list * ScmRewriteState<'subState>) =
            let mutable varState = state
            let mutable newFields = []
            for i in basedOn do
                let (newField,newState) = runState (getUnusedFieldName i) varState
                varState <- newState
                newFields <- newField::newFields
            (List.rev newFields, varState)
        ScmRewriteFunction (newUnusedFieldNames)

        
    let getSubComponentToChange<'subState> : ScmRewriteFunction<'subState,CompDecl> = 
        let getParentCompDecl (state:ScmRewriteState<'subState>) : (CompDecl * ScmRewriteState<'subState>) =
            state.ChangingSubComponent,state
        ScmRewriteFunction (getParentCompDecl)
        
        
    let getPathOfSubComponentToChange<'subState> : ScmRewriteFunction<'subState,CompPath> = 
        let getPathOfSubComponentToChange (state:ScmRewriteState<'subState>) : (CompPath * ScmRewriteState<'subState>) =
            state.PathOfChangingSubcomponent,state
        ScmRewriteFunction (getPathOfSubComponentToChange)

        
    let updateSubComponentToChange<'subState> (updatedSubComponent:CompDecl) : ScmRewriteFunction<'subState,unit> = 
        let updateSubComponentToChange (state:ScmRewriteState<'subState>) : (unit * ScmRewriteState<'subState>) =
            let newState =
                { state with
                    ScmRewriteState.ChangingSubComponent = updatedSubComponent;
                    ScmRewriteState.Tainted = true;
                }
            (),newState
        ScmRewriteFunction (updateSubComponentToChange)

    // TODO: Move every access to the model into a function here.
    //       Here we can easily assure, that reading operations occur on the correct part of the model (which may
    //       live in the rewritten part). Also buffering/caching operations can be implemented here more easily.


        
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Check Consistency
    //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    let checkConsistency<'subState> : ScmRewriteFunction<'subState,unit> = scmRewrite {
            return ()
        }
    
