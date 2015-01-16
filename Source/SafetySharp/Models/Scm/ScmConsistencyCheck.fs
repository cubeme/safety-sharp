// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

module internal ScmConsistencyCheck =
    open ScmHelpers

    
    let rec checkIfStatementCallsNoDelayedPortTransient (model:CompDecl) (compPath:CompPath) (stm:Stm) : bool =
        // Return true, if no DelayedPort is called.    
        // need the complete model, because a relevant binding might be declared in the parent node
        match stm with
            | Stm.AssignVar (_) -> true
            | Stm.AssignField (_) -> true
            | Stm.AssignFault (_) -> true
            | Stm.Block (stmts) ->
                stmts |> List.forall (fun stm -> checkIfStatementCallsNoDelayedPortTransient model compPath stm)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                choices |> List.forall (fun (guard,stm) -> checkIfStatementCallsNoDelayedPortTransient model compPath stm)
            | Stm.StepComp (comp) ->
                let newPath = comp::compPath
                let compDecl = model.getDescendantUsingPath newPath
                compDecl.Steps |> List.forall (fun step -> checkIfStatementCallsNoDelayedPortTransient model compPath step.Behavior.Body)
            | Stm.StepFault (fault) ->
                let compDecl = model.getDescendantUsingPath compPath
                let faults =
                    compDecl.Faults |> List.filter (fun faultDecl -> faultDecl.Fault = fault)
                faults |> List.forall (fun fault -> checkIfStatementCallsNoDelayedPortTransient model compPath fault.Step.Body)
            | Stm.CallPort (reqPort,_params) ->
                let bndDeclPath = model.tryFindBindingOfReqPort (compPath,reqPort)
                match bndDeclPath with
                    | None ->
                        // Binding could not be found: Model is incomplete. But: it is not because of a DelayedPort ;-)
                        true
                    | Some(bndDeclCompPath,binding) ->
                        let provPortPath = model.tryGetProvPort (bndDeclCompPath,binding)
                        match provPortPath with
                            | None ->
                                true
                            | Some(provPortPath,provPort) ->
                                let provPortCompDecl = model.getDescendantUsingPath provPortPath
                                provPortCompDecl.getProvPortDecls(provPort)
                                    |> List.forall (fun provPort -> checkIfStatementCallsNoDelayedPortTransient model provPortPath provPort.Behavior.Body)
            
    let rec checkIfProvPortCallsNoDelayedPortTransient (model:CompDecl) (compPath:CompPath) (provPort:ProvPort) =
        let provPortCompDecl = model.getDescendantUsingPath compPath
        provPortCompDecl.getProvPortDecls(provPort)
            |> List.forall (fun provPort -> checkIfStatementCallsNoDelayedPortTransient model compPath provPort.Behavior.Body)
