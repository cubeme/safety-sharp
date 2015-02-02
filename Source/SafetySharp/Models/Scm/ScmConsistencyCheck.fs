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


// TODO:
// Checks can be divided into several groups
//   * Something, which can be checked, without knowing "something" in the parent (Entity-Local)
//   * Something, which needs the whole _component_, where it is defined (Component-Local)
//   * Something, which needs the whole _model_ (Model-Global)
//     In this group walkers over statements and collections are useful
//     This group can also reuse elements from entity-local

namespace SafetySharp.Models
open SafetySharp.Models.Scm
open SafetySharp.Models.ScmHelpers

module internal ScmConsistencyCheck =

    /////////////
    // generic function for Statements
    ////////////
    
    type CheckerAtomarAssessor = Stm->(bool*bool) // statement -> (keepOnWalking,result)
    
    let ``generic function to check if statement satisfies condition (transitive)``
           (assessor:CheckerAtomarAssessor) (model:CompDecl) (compPath:CompPath) (stm:Stm) : bool =
        
        let walkerAssessor (stm:Stm,oldValue:bool) : (bool*bool) =
            assessor stm // do not use the old Value
        let neutralValue = true // List.forall (fun ...) [] = true
        let selectValue = List.forall //everything in the sub nodes must be true, that the checker returns true.
        let oldValue = true // we ignore the old value. could also be "false"
        stmTransitiveWalker walkerAssessor selectValue neutralValue model compPath oldValue stm
    

            
    /////////////
    // single checks for statements
    ////////////
    
    let ``check if Stm makes no delayed call (transitive)`` (model:CompDecl) (compPath:CompPath) (stm:Stm) : bool =
        // Return true, if at no DelayedPort is called.    
        let walkerAssessor (stm:Stm,oldValue:bool) : (bool*bool) = //returns (keepOnWalking,newValue)
            match stm with                
                | Stm.AssignVar (_) -> false,true // stop walking, and everything is fine
                | Stm.AssignField (_) -> false,true // stop walking, and everything is fine
                | Stm.AssignFault (_) -> false,true // stop walking, and everything is fine
                | Stm.Block (_) -> true,true // keep on walking
                | Stm.Choice (_) -> true,true  // keep on walking
                | Stm.StepComp (_) -> true,true // keep on walking
                | Stm.StepFault (_) -> true,true // keep on walking
                | Stm.CallPort (reqPort,_params) ->
                    let bndDeclPath = model.tryFindBindingOfReqPort (compPath,reqPort)
                    match bndDeclPath with
                        | None -> 
                            // Binding could not be found: Model is incomplete. But: it is not because of a DelayedPort
                            false,true //stop walking, the rule check itself succeeds
                        | Some(bndDeclCompPath,binding) ->
                            if binding.Kind = BndKind.Delayed then
                                false,false   // <------------ this is what we are searching for. Stop the search and return false
                            else 
                                true,true //keep on walking, the rule check itself succeeds
        let neutralValue = true // List.forall (fun ...) [] = true
        let selectValue = List.forall //everything in the sub nodes must be true, that the checker returns true.
        let oldValue = true // we ignore the old value. could also be "false"
        stmTransitiveWalker walkerAssessor selectValue neutralValue model compPath oldValue stm

        
    let ``check if Stm makes at most one delayed call (transitive)`` (model:CompDecl) (compPath:CompPath) (stm:Stm) : bool =
        // Return true, if at most one DelayedPort is called.    
        // first construct every continuation for the stmWalker
        // the walker should return the maximal depth of calls of delayed bindings. But it should also stop
        // as soon as it reaches the depth 2
        // Note: If this gets an efficiency bottleneck it can be implemented faster with the Floyd-Warshall-Algorithm
        let stopValue = 2
        let walkerAssessor (stm:Stm,oldValue:int) : (bool*int) = //returns (keepOnWalking,number of delayed Port Calls)
            match stm with                
                | Stm.AssignVar (_) -> false,oldValue // stop walking, and everything is fine
                | Stm.AssignField (_) -> false,oldValue // stop walking, and everything is fine
                | Stm.AssignFault (_) -> false,oldValue // stop walking, and everything is fine
                | Stm.Block (_) -> true,oldValue // keep on walking
                | Stm.Choice (_) -> true,oldValue  // keep on walking
                | Stm.StepComp (_) -> true,oldValue // keep on walking
                | Stm.StepFault (_) -> true,oldValue // keep on walking
                | Stm.CallPort (reqPort,_params) ->
                    let bndDeclPath = model.tryFindBindingOfReqPort (compPath,reqPort)
                    match bndDeclPath with
                        | None -> 
                            // Binding could not be found: Model is incomplete. But: it is not because of a DelayedPort
                            false,oldValue //stop walking, the rule check itself succeeds
                        | Some(bndDeclCompPath,binding) ->
                            if binding.Kind = BndKind.Delayed then
                                // this is what we are searching for
                                let numberOfDelayedPortCalls = oldValue + 1
                                let goOnWalking = numberOfDelayedPortCalls < stopValue
                                goOnWalking,numberOfDelayedPortCalls
                            else 
                                true,oldValue //keep on walking, the rule check itself succeeds
        let neutralValue = 0 // List.forall (fun ...) [] = 0        
        // type WalkerReductionAssessor<'a> = (Stm -> 'a) -> Stm list -> 'a
        let rec selectValue (assessStatement:Stm->int) (stmnts:Stm list) : int =
            // take the maximal value of the list. If List is empty, use neutralValue
            if stmnts.IsEmpty then
                neutralValue
            else
                let valueOfHead = assessStatement stmnts.Head
                let valueOfTail = selectValue assessStatement stmnts.Tail //not tail recursive
                let goOnWalking = valueOfHead < stopValue
                if goOnWalking=false then
                    valueOfHead //early quit
                else
                    max valueOfHead valueOfTail
        let oldValue = 0 // initially 0 delayed ports where called
        // now call the stmWalker with all values and continuations
        let depthUntilStopValue =   
            stmTransitiveWalker walkerAssessor selectValue neutralValue model compPath oldValue stm
        // use the result of the walker to determine if our check succeeded
        (depthUntilStopValue <= 1)



    let ``check if Stm never writes to a field/fault and never reads a variable (transitive)`` (model:CompDecl) (compPath:CompPath) (stm:Stm) : bool =
        // return true, if never written to a field and never reading a variable
        // also need to check expressions
        let rec checkExpression (expr:Expr) : bool =
            match expr with
                | Literal (_) -> true
                | ReadVar (_) -> false //read var is forbidden
                | ReadField (_) -> true
                | UExpr (expr,_) -> checkExpression expr
                | BExpr (leftExpr,_,rightExpr) -> (checkExpression leftExpr) && (checkExpression rightExpr)                
        let checkParams (_param:Param) : bool =
            match _param with
                | Param.ExprParam (expr) -> checkExpression expr
                | Param.InOutFieldParam (_) -> false
                | Param.InOutVarParam (_) -> true
        let walkerAssessor (stm:Stm) : (bool*bool) = // statement -> (keepOnWalking,result)
            match stm with
                | AssignVar (var, expr) -> (false,checkExpression expr)
                | AssignField (_) -> false,false
                | AssignFault (_,expr) -> false,false
                | Block (_) -> true,true
                | Choice (choices:(Expr * Stm) list) ->
                    let guardsAreOkay = choices |> List.forall (fun (guard,_)-> checkExpression guard)
                    (true,guardsAreOkay)
                | CallPort (_,_params:Param list) ->
                    let paramsAreOkay = _params |> List.forall (fun _param -> checkParams _param)
                    (true,paramsAreOkay)
                | StepComp (comp) -> true,true
                | StepFault (fault) -> true,true
        ``generic function to check if statement satisfies condition (transitive)`` walkerAssessor model compPath stm 


    (*
    TODO: Remove, if no use
    /////////////
    // single checks for ProvPorts
    ////////////
        
    let ``check ProvPorts of model's root with stm-checker (transitive)`` (checkStm:CompDecl->CompPath->Stm->bool) (model:CompDecl) =
        let checkStm = checkStm model [model.Comp] //abbrev
        model.ProvPorts |> List.forall (fun step -> checkStm step.Behavior.Body)

        
    let ``check if ProvPort in compPath makes no delayed call (transitive)`` (model:CompDecl) (compPath:CompPath) (provPort:ProvPort) =
        let provPortCompDecl = model.getDescendantUsingPath compPath
        provPortCompDecl.getProvPortDecls(provPort)
            |> List.forall (fun provPort -> ``check if Stm makes no delayed call (transitive)`` model compPath provPort.Behavior.Body)
            
    let ``check if ProvPorts of model's root make at most one delayed call (transitive)`` (model:CompDecl) : bool =
        ``check ProvPorts of model's root with stm-checker (transitive)`` ``check if Stm makes at most one delayed call (transitive)`` model
    *)  



    /////////////
    // single checks for the Main Steps
    ////////////
    
    let ``check Steps of model's root with stm-checker (transitive)`` (checkStm:CompDecl->CompPath->Stm->bool) (model:CompDecl) =
        let checkStm = checkStm model [model.Comp] //abbrev
        model.Steps |> List.forall (fun step -> checkStm step.Behavior.Body)
        
    let ``check if Main Steps make at most one delayed call (transitive)`` (model:CompDecl) : bool =
        ``check Steps of model's root with stm-checker (transitive)`` ``check if Stm makes at most one delayed call (transitive)`` model
        
    //let ``check if Delay Port Main Steps make at most one delayed call (transitive)`` (model:CompDecl) : bool =
    //    ``check Steps of model's root with stm-checker (transitive)`` ``check if Stm never writes to a field/fault and never reads a variable (transitive)`` model
        
               

    /////////////
    // single checks for BehaviorWithLocation
    ////////////
    
    // generic
    
    let ``check BehaviorOfLocation with stm-checker (transitive)`` (checkStm:CompDecl->CompPath->Stm->bool) (model:CompDecl) (locBeh:BehaviorWithLocation) =
        checkStm model locBeh.Location locBeh.Behavior.Body

    let ``check BehaviorOfLocations with stm-checker (transitive)`` (checkStm:CompDecl->CompPath->Stm->bool) (model:CompDecl) (locBehs:BehaviorWithLocation list) =
        locBehs |> List.forall (fun locBeh -> checkStm model locBeh.Location locBeh.Behavior.Body)
                    
    // actual
    
    let ``check if BehaviorOfLocations make at most one delayed call (transitive)`` (model:CompDecl) (locBeh:BehaviorWithLocation) =
        ``check BehaviorOfLocations with stm-checker (transitive)`` ``check if Stm makes at most one delayed call (transitive)``

    
    /////////////
    // single checks for ProvPorts
    ////////////
    
    let ``check if ProvPortDecl has no In parameter`` (provPortDecl:ProvPortDecl) =
        provPortDecl.Params |> List.forall (fun param -> param.Dir <> ParamDir.In)
        
    //let ``check if all ProvPortDecls with the same ProvPort have the same signature`` =
    //    false
