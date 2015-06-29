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

module internal ScmRewriterRemoveGivenFaults =
    open SafetySharp.Models.ScmTracer
    open SafetySharp.Workflow
    open SafetySharp.Models.Scm
    open SafetySharp.Models.ScmHelpers
    
    
    let rec removeFaultsFromStm (faultsToRemoveInCurrentComponent:Set<Fault>) (stm:Stm) : Stm =        
        let keepStmInBlock (stm:Stm) : bool =
            match stm with
                | Stm.StepFault (fault) -> if faultsToRemoveInCurrentComponent.Contains fault then false else true
                | Stm.AssignFault (fault, expr) -> if faultsToRemoveInCurrentComponent.Contains fault then false else true
                | _ -> true

        let removeFaultsFromStm = removeFaultsFromStm faultsToRemoveInCurrentComponent
        match stm with
            | Stm.AssignVar (var,expr) -> stm
            | Stm.AssignField (field, expr) -> stm
            | Stm.AssignFault (fault, expr) ->
                if faultsToRemoveInCurrentComponent.Contains fault then
                    Stm.Block([])
                else
                    stm
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.filter keepStmInBlock |> List.map removeFaultsFromStm
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (expr,removeFaultsFromStm stm) )
                Stm.Choice(newChoices)
            | Stm.Stochastic (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (expr,removeFaultsFromStm stm) )
                Stm.Stochastic(newChoices)
            | Stm.CallPort (reqPort,_params) ->
                stm
            | Stm.StepComp (comp) ->
                stm
            | Stm.StepFault (fault) ->
                if faultsToRemoveInCurrentComponent.Contains fault then
                    Stm.Block([])
                else
                    stm

    let removeFaultsFromBehavior (faultsToRemoveInCurrentComponent:Set<Fault>) (behavior:BehaviorDecl) : BehaviorDecl =
        { behavior with
            BehaviorDecl.Body = removeFaultsFromStm faultsToRemoveInCurrentComponent behavior.Body
        }
    
    let keep_easyFilterFromOptFaultExpr (faultsToRemoveInCurrentComponent:Set<Fault>) (faultExpr:FaultExpr option) : bool =
        let rec decideOnSimpleStructure (faultExpr:FaultExpr) : bool =
            match faultExpr with
                | FaultExpr.Fault (fault) ->
                    not(faultsToRemoveInCurrentComponent.Contains fault)
                | FaultExpr.NotFault (faultExpr) ->
                    true
                | FaultExpr.AndFault (faultExprLeft,(faultExprRight)) ->
                    let resultForLeft = decideOnSimpleStructure faultExprLeft
                    let resultForRight = decideOnSimpleStructure faultExprRight
                    if (resultForLeft=false) || (resultForRight=false) then
                        false
                    else
                        true
                | FaultExpr.OrFault (faultExprLeft,(faultExprRight)) ->
                    true
        match faultExpr with
            | None -> true
            | Some(faultExpr) -> decideOnSimpleStructure faultExpr
                

    let rec removeFaultsFromFaultExpr (faultsToRemoveInCurrentComponent:Set<Fault>) (faultExpr:FaultExpr option) : FaultExpr option =
        failwith "NotImplementedYet"
        // TODO: Here we have to replace every faultsToRemoveInCurrentComponent by a virtual "False". The difficulty is that
        // we need to propagate the changes up, because we have no "False"
        
    let rec removeFaultsFromContract (faultsToRemoveInCurrentComponent:Set<Fault>) (contract:Contract) : Contract =
        match contract with
            | Contract.None -> contract
            | _ -> failwith "NotImplementedYet"


    let rec removeFaultsFromCompDecl (faultsToRemove:Map<CompPath,Set<Fault>>) (parentPath:CompPath) (compDecl:CompDecl) : CompDecl =
        let currentPath = compDecl.Comp :: parentPath
        let faultsToRemoveInCurrentComponent = if faultsToRemove.ContainsKey currentPath then faultsToRemove.Item currentPath else Set.empty<Fault>
        let keep_easyFilterFromOptFaultExpr = keep_easyFilterFromOptFaultExpr faultsToRemoveInCurrentComponent
        { compDecl with
            CompDecl.Subs =
                compDecl.Subs |> List.map (removeFaultsFromCompDecl faultsToRemove currentPath)
            CompDecl.Fields =
                compDecl.Fields;
            CompDecl.Faults =
                let isFaultKept (fault:FaultDecl) : bool=
                    not(faultsToRemoveInCurrentComponent.Contains fault.Fault)
                let faultsToKeep = compDecl.Faults |> List.filter isFaultKept
                let rewriteFault (faultDecl:FaultDecl) : FaultDecl = 
                    { faultDecl with
                        FaultDecl.Step = removeFaultsFromBehavior faultsToRemoveInCurrentComponent faultDecl.Step
                    }
                faultsToKeep |> List.map rewriteFault;
            CompDecl.ProvPorts =
                let provPortsToKeep = compDecl.ProvPorts |> List.filter (fun provPort -> keep_easyFilterFromOptFaultExpr provPort.FaultExpr)
                let rewriteProvPort (provPortDecl:ProvPortDecl) : ProvPortDecl = 
                    { provPortDecl with
                        ProvPortDecl.Behavior = removeFaultsFromBehavior faultsToRemoveInCurrentComponent provPortDecl.Behavior;
                        ProvPortDecl.FaultExpr = removeFaultsFromFaultExpr faultsToRemoveInCurrentComponent provPortDecl.FaultExpr
                        ProvPortDecl.Contract = removeFaultsFromContract faultsToRemoveInCurrentComponent provPortDecl.Contract
                    }
                provPortsToKeep |> List.map rewriteProvPort;
            CompDecl.Steps =            
                let stepsToKeep = compDecl.Steps  |> List.filter (fun step -> keep_easyFilterFromOptFaultExpr step.FaultExpr)
                let rewriteStep (stepDecl:StepDecl) : StepDecl = 
                    { stepDecl with
                        StepDecl.Behavior = removeFaultsFromBehavior faultsToRemoveInCurrentComponent stepDecl.Behavior;
                        StepDecl.FaultExpr = removeFaultsFromFaultExpr faultsToRemoveInCurrentComponent stepDecl.FaultExpr
                        StepDecl.Contract = removeFaultsFromContract faultsToRemoveInCurrentComponent stepDecl.Contract
                    }
                stepsToKeep |> List.map rewriteStep;
        }

    let locatedFaultsToRemove (faultsToRemove:FaultPath list) : Map<CompPath,Set<Fault>> =
        let addToFaultsToRemoveMap (acc:Map<CompPath,Set<Fault>>) (faultToRemoveComp:CompPath,faultToRemoveFault:Fault) : Map<CompPath,Set<Fault>> =
            if acc.ContainsKey faultToRemoveComp then
                let oldSet = acc.Item faultToRemoveComp
                let newSet = oldSet.Add(faultToRemoveFault)
                acc.Add(faultToRemoveComp,newSet)
            else
                let newSet = Set.empty<Fault>.Add(faultToRemoveFault)
                acc.Add(faultToRemoveComp,newSet)
        faultsToRemove |> List.fold addToFaultsToRemoveMap (Map.empty<CompPath,Set<Fault>>)
    
    let removeFaults<'traceableOfOrigin,'oldState when 'oldState :> IScmTracer<'traceableOfOrigin,'oldState>> (faultsToRemove:FaultPath list)  ()
                        : ExogenousWorkflowFunction<'oldState,SimpleScmTracer<'traceableOfOrigin>> = workflow {        
        do! iscmToSimpleScmTracer ()
        
        let! model = iscmGetModel ()
        let newScmModel = 
            let locatedFaultsToRemove = locatedFaultsToRemove faultsToRemove
            let newRootComp = removeFaultsFromCompDecl locatedFaultsToRemove [] (model.getRootComp)
            ScmModel.ScmModel(newRootComp )
                        
        do! iscmSetModel newScmModel

        let iscmTraceFault (fault:FaultPath) =
            iscmTraceTraceable (Scm.Traceable.TraceableFault(fault)) (Scm.Traceable.TraceableRemoved("fault was removed with ScmRewriterRemoveGivenFaults") )
        do! listIter_seqState iscmTraceFault faultsToRemove
    }


