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

module internal ScmHelpers =

    type CompPath = Comp list
    type FieldPath = CompPath * Field
    type FaultPath = CompPath * Fault
    type ReqPortPath = CompPath * ReqPort
    type ProvPortPath = CompPath * ProvPort

    type StmPath = int list // index1::index2::[] -> Blockstatement2=Blockstatement1.[index2] ; Stm=Blockstatement2.[index1] ; Stm=Blockstatement1.[index2].[index1]
    
    
    // Extension methods
    type Stm with
        member stm.getSubStatement (path:StmPath) : Stm =
            if path = [] then
                stm
            else
                match stm with
                    | Stm.Block (stmts) ->
                        let subStatement = List.nth stmts path.Head
                        subStatement.getSubStatement path.Tail                        
                    | Stm.Choice (choices:(Expr * Stm) list) ->
                        let (expr,stm) = List.nth choices path.Head
                        stm.getSubStatement path.Tail
                    | _ -> failwith "Try to get a SubStatement from a non Block/Choice Statement"
        member stm.replaceSubStatement (path:StmPath) (replaceBy:Stm) : Stm =
            if path = [] then
                replaceBy
            else
                match stm with
                    | Stm.Block (stmts) ->
                        let stmIndex = path.Head
                        let subStatement = List.nth stmts stmIndex
                        let newSubStatement = subStatement.replaceSubStatement path.Tail replaceBy
                        let newStmnts = ( List.map2 (fun index stm -> if index<>stmIndex then stm else newSubStatement) ([0..(stmts.Length-1)]) (stmts) );
                        Stm.Block (newStmnts)
                    | Stm.Choice (choices:(Expr * Stm) list) ->
                        let stmIndex = path.Head
                        let (expr,subStatement) = List.nth choices stmIndex
                        let newSubStatement = subStatement.replaceSubStatement path.Tail replaceBy
                        let newChoices = ( List.map2 (fun index (guard,stm) -> if index<>stmIndex then (guard,stm) else (guard,newSubStatement)) ([0..(choices.Length-1)]) (choices) );
                        Stm.Choice(newChoices)
                    | _ -> failwith "Try to replace a SubStatement from a non Block/Choice Statement"
               

    // Extension methods
    type Var with
        member var.getName =
            match var with
                | Var.Var (name) -> name

    // Extension methods
    type VarDecl with
        member var.getName =
            var.Var.getName

    // Extension methods
    type Field with
        member field.getName =
            match field with
                | Field.Field (name) -> name

    // Extension methods
    type FieldDecl with
        member field.getName =
            field.Field.getName
        
    // Extension methods
    type ReqPort with
        member reqPort.getName =
            match reqPort with
                | ReqPort.ReqPort (name) -> name

    // Extension methods
    type ParamDecl with
        member param.getName =
            param.Var.getName

    // Extension methods
    type ReqPortDecl with
        member reqPort.getName =
            reqPort.ReqPort.getName
            
    // Extension methods
    type ProvPort with
        member provPort.getName =
            match provPort with
                | ProvPort.ProvPort (name) -> name

    // Extension methods
    type ProvPortDecl with
        member provPort.getName =
            provPort.ProvPort.getName
            
    // Extension methods
    type Fault with
        member fault.getName =
            match fault with
                | Fault.Fault (name) -> name

    // Extension methods
    type FaultDecl with
        member fault.getName =
            fault.Fault.getName
            
    // Extension methods
    type Comp with
        member comp.getName =
            match comp with
                | Comp.Comp (name) -> name
                
    // Extension methods
    type CompDecl with
        member node.getName =
            node.Comp.getName

        // rev_path = root :: ... :: parent_of_leaf :: leaf
        member node.getDescendantUsingRevPath (rev_path: Comp list) : CompDecl =
            if rev_path.IsEmpty then
                node
            else
                let subComponent =
                    node.Subs |> List.find (fun elem -> elem.Comp = rev_path.Head)
                subComponent.getDescendantUsingRevPath rev_path.Tail
    
        // path = leaf :: parent_of_leaf :: ... :: root
        member node.getDescendantUsingPath (path: Comp list) : CompDecl =
            let reverseList = List.rev path
            assert (reverseList.Head = node.Comp)
            node.getDescendantUsingRevPath reverseList.Tail
        
        member node.getTakenNames () : string list =
            let namesInFields = node.Fields |> List.map(fun field -> field.getName)
            let namesInFaults =
                let nameInFault (fault:FaultDecl) =
                    let nameOfLocalVar = fault.Step.Locals |> List.map (fun var -> var.getName )
                    let nameOfFault = fault.getName
                    nameOfFault:: nameOfLocalVar
                node.Faults |> List.collect nameInFault
            let namesInReqPorts = node.ReqPorts |> List.map (fun reqPort -> reqPort.getName)
            let namesInProvPorts =
                let namesInProvPort (provPort:ProvPortDecl) : string list =
                    let namesInParameter = provPort.Params |> List.map (fun param -> param.getName )
                    let namesInLocalVar = provPort.Behavior.Locals |> List.map (fun var -> var.getName)
                    let nameOfPort = provPort.getName
                    nameOfPort :: namesInParameter @ namesInLocalVar
                node.ProvPorts |> List.collect namesInProvPort
            let namesInSteps =
                let namesInStep (step:StepDecl) =
                    step.Behavior.Locals |> List.map (fun var -> var.getName )
                node.Steps |> List.collect namesInStep
            namesInFields @ namesInFaults @ namesInReqPorts @ namesInProvPorts @ namesInSteps
            

        (*
        member node.getParentOfDescendantUsingPath (path: Comp list) : CompDecl =
            // minimal path size is 2
            let listWithoutChild = path.Tail
            let reverseList = List.rev listWithoutChild
            assert (reverseList.Head = node.Comp)
            node.getDescendantUsingRevPath reverseList.Tail
        *)
        member node.removeField (field:FieldDecl) =
            { node with
                CompDecl.Fields = (node.Fields |> List.filter (fun _field -> field<>_field));
            }
        member node.addField (field:FieldDecl) =
            { node with
                CompDecl.Fields = field::node.Fields
            }
                                
        member node.removeFault (fault:FaultDecl) =
            { node with
                CompDecl.Faults = (node.Faults |> List.filter (fun _fault -> fault<>_fault));
            }
        member node.addFault (fault:FaultDecl) =
            { node with
                CompDecl.Faults = fault::node.Faults
            }
        member node.replaceFault (faultToReplace:FaultDecl, newFault:FaultDecl) =
            { node with
                CompDecl.Faults = (node.Faults |> List.map (fun fault -> if fault=faultToReplace then newFault else fault));
            }

        member node.removeReqPort (reqPort:ReqPortDecl) =
            { node with
                CompDecl.ReqPorts = (node.ReqPorts |> List.filter (fun _reqPort -> reqPort<>_reqPort));
            }
        member node.addReqPort (reqPort:ReqPortDecl) =
            { node with
                CompDecl.ReqPorts = reqPort::node.ReqPorts
            }
                
        member node.removeProvPort (provPort:ProvPortDecl) =
            { node with
                CompDecl.ProvPorts = (node.ProvPorts |> List.filter (fun _provPort -> provPort<>_provPort));
            }
        member node.addProvPort (fault:ProvPortDecl) =
            { node with
                CompDecl.ProvPorts = fault::node.ProvPorts
            }
        member node.replaceProvPort (provPortToReplace:ProvPortDecl, newProvPort:ProvPortDecl) =
            { node with
                CompDecl.ProvPorts = (node.ProvPorts |> List.map (fun provPort -> if provPort=provPortToReplace then newProvPort else provPort));
            }            
        member node.getProvPortDecls (provPort:ProvPort) : ProvPortDecl list =
            node.ProvPorts |> List.filter (fun _provPort -> _provPort.ProvPort = provPort)
                
        member node.removeBinding (bndg:BndDecl) =
            { node with
                CompDecl.Bindings = (node.Bindings |> List.filter (fun _binding -> _binding<>bndg));
            }
        member node.addBinding (bndg:BndDecl) =
            { node with
                CompDecl.Bindings = bndg::node.Bindings
            }  
        member node.replaceBinding (bindingToReplace:BndDecl, newBinding:BndDecl) =
            { node with
                CompDecl.Bindings = (node.Bindings |> List.map (fun bndg -> if bndg=bindingToReplace then newBinding else bndg));
            }
        member node.getBindingOfLocalReqPort (reqPort:ReqPort) : BndDecl=
            node.Bindings |> List.find (fun bndg -> bndg.Target.ReqPort=reqPort && bndg.Target.Comp=None)
            
        member node.removeStep (step:StepDecl) =
            { node with
                CompDecl.Steps = (node.Steps |> List.filter (fun _step -> _step<>step));
            }    
        member node.replaceStep (stepToReplace:StepDecl, newStep:StepDecl) =
            { node with
                CompDecl.Steps = (node.Steps |> List.map (fun step -> if step=stepToReplace then newStep else step));
            }     
                                    
        member node.removeChild (child:CompDecl) =
            { node with
                CompDecl.Subs = (node.Subs |> List.filter (fun _child -> _child<>child));
            }        
        member node.replaceChild (childToReplace:CompDecl, newChild:CompDecl) =
            { node with
                CompDecl.Subs = (node.Subs |> List.map (fun child -> if child=childToReplace then newChild else child));
            }

        member node.replaceChild (childToReplace:Comp, newChild:CompDecl) =
            { node with
                CompDecl.Subs = (node.Subs |> List.map (fun child -> if child.Comp=childToReplace then newChild else child));
            }


        // Complete model        
        member model.replaceDescendant (pathToReplace: Comp list) (newComponent:CompDecl) : CompDecl =
            if pathToReplace.Head = model.Comp && pathToReplace.Tail = [] then
                //root should be replaced
                newComponent
            else
                //parent: We get the parent, where we correct the old node with the new node
                let parentPath = pathToReplace.Tail
                let parentNode = model.getDescendantUsingPath parentPath
                let nodeToReplace = pathToReplace.Head
                let newParent = parentNode.replaceChild(nodeToReplace,newComponent)
                // recursively replace parent
                model.replaceDescendant pathToReplace.Tail newParent


                
    // some local helpers
    let rec rewriteFaultExpr (faultMap:Map<Fault,Fault>) (faultExpr:FaultExpr) = //from->to
        let rewriteFault (fault) : Fault =
            faultMap.Item fault
        match faultExpr with
            | FaultExpr.Fault (fault) -> FaultExpr.Fault (rewriteFault fault)
            | FaultExpr.NotFault (faultExpr) -> FaultExpr.NotFault(rewriteFaultExpr faultMap faultExpr)
            | FaultExpr.AndFault (left,right) -> FaultExpr.AndFault (rewriteFaultExpr faultMap left, rewriteFaultExpr faultMap right)
            | FaultExpr.OrFault (left,right) -> FaultExpr.OrFault (rewriteFaultExpr faultMap left, rewriteFaultExpr faultMap right)

    let rewriteFaultExprOption (faultMap:Map<Fault,Fault>) (faultExpr:FaultExpr option) =
        match faultExpr with
            | None -> None
            | Some (faultExpr) -> Some (rewriteFaultExpr faultMap faultExpr)
                    
    let rec rewriteExpr (varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (expr:Expr) : Expr=
        match expr with
            | Expr.Literal (_val) -> Expr.Literal(_val)
            | Expr.ReadVar (_var) ->
                let newVar=varMap.Item _var
                Expr.ReadVar (newVar)
            | Expr.ReadField (field) ->
                let newField=fieldMap.Item field
                Expr.ReadField (newField)
            | Expr.UExpr (expr,uop) -> Expr.UExpr(rewriteExpr (varMap,fieldMap) expr,uop)
            | Expr.BExpr (left, bop, right) -> Expr.BExpr(rewriteExpr (varMap,fieldMap) left,bop,rewriteExpr (varMap,fieldMap) right)

    let rewriteParam (varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (_param:Param) : Param =
        match _param with
            | Param.ExprParam (expr) -> Param.ExprParam(rewriteExpr (varMap,fieldMap) expr)
            | Param.InOutVarParam (var) ->
                let newVar = varMap.Item var
                Param.InOutVarParam (newVar)
            | Param.InOutFieldParam (field) ->                    
                let newField = fieldMap.Item(field)
                Param.InOutFieldParam (newField)

    let rec rewriteStm (reqPortMap:Map<ReqPort,ReqPort>,faultMap:Map<Fault,Fault>,varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (stm:Stm) : Stm =
        match stm with
            | Stm.AssignVar (var,expr) ->
                let newExpr = rewriteExpr (varMap,fieldMap) expr
                let newVar = varMap.Item var
                Stm.AssignVar (newVar, newExpr)
            | Stm.AssignField (field, expr) ->
                let newField = fieldMap.Item(field)
                let newExpr = rewriteExpr (varMap,fieldMap) expr
                Stm.AssignField (newField, newExpr)
            | Stm.AssignFault (fault, expr) ->
                let newFault = faultMap.Item(fault)
                let newExpr = rewriteExpr (varMap,fieldMap)  expr
                Stm.AssignFault (newFault, newExpr)
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.map (rewriteStm (reqPortMap,faultMap,varMap,fieldMap))
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (rewriteExpr (varMap,fieldMap)  expr,rewriteStm (reqPortMap,faultMap,varMap,fieldMap) stm) )
                Stm.Choice(newChoices)
            | Stm.CallPort (reqPort,_params) ->
                let newReqPort = reqPortMap.Item (reqPort)
                let newParams = _params |> List.map (rewriteParam (varMap,fieldMap) )
                Stm.CallPort (newReqPort,newParams)
            | Stm.StepComp (comp) ->
                Stm.StepComp (comp)
            | Stm.StepFault (fault) ->
                let newFault = faultMap.Item(fault)
                Stm.StepFault (newFault)

    let rewriteBehavior (reqPortMap:Map<ReqPort,ReqPort>,faultMap:Map<Fault,Fault>,varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (behavior:BehaviorDecl) =
        {
            BehaviorDecl.Locals= behavior.Locals; // The getUnusedxxxName-Functions also ensured, that the names of new fields and faults,... do not overlap with any local variable. So we can keep it
            BehaviorDecl.Body = rewriteStm (reqPortMap,faultMap,varMap,fieldMap) behavior.Body;
        }