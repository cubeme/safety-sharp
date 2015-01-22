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

module internal ScmHelpers =
    
    
    type CompPath = Comp list
        // index1::index2::root::[]
        // root {
        //   index2 {
        //     index1 {
        //       ...
        //     }
        //     ...
        //   }
        //   ...
        // }

    type FieldPath = CompPath * Field
    type FaultPath = CompPath * Fault
    type ReqPortPath = CompPath * ReqPort
    type ProvPortPath = CompPath * ProvPort
    type BndDeclPath = CompPath * BndDecl



    type StmPath = int list
        // index1::index2::[]
        // Example:
        //    Block{
        //       Stm1;              // 0::[]
        //       Stm2;              // 1::[]
        //       Stm3;              // 2::[]
        //       Choice {           // 3::[]
        //           Guard,Stm 4.1  // 3::0::[]
        //           Guard,Stm 4.2  // 3::1::[]
        //       }
    
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
    type Type with
        member _type.getDefaultInitVal =
            match _type with
                | Type.BoolType -> Val.BoolVal(true)
                | Type.IntType -> Val.IntVal(0)

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
    type Param with
        member param.IsExpr =
            match param with
                | ExprParam (_) -> true
                | _ -> false
        member param.IsInOutVar =
            match param with
                | InOutVarParam (_) -> true
                | _ -> false
        member param.IsInOutField =
            match param with
                | InOutFieldParam (_) -> true
                | _ -> false

    
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
    type FaultExpr with
        member faultExpr.rewrite_toExpr (faultMap:Map<Fault,Field>) : Expr =
            match faultExpr with
                | Fault (fault) ->
                    Expr.ReadField(faultMap.Item fault)
                | NotFault (faultExpr) ->
                    Expr.UExpr(faultExpr.rewrite_toExpr faultMap,UOp.Not)
                | AndFault (leftFaultExpr,rightFaultExpr) ->
                    Expr.BExpr(leftFaultExpr.rewrite_toExpr faultMap,BOp.And,rightFaultExpr.rewrite_toExpr faultMap)
                | OrFault (leftFaultExpr,rightFaultExpr) ->
                    Expr.BExpr(leftFaultExpr.rewrite_toExpr faultMap,BOp.Or,rightFaultExpr.rewrite_toExpr faultMap)

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
            

        member node.removeField (field:FieldDecl) =
            { node with
                CompDecl.Fields = (node.Fields |> List.filter (fun _field -> field<>_field));
            }
        member node.addField (field:FieldDecl) =
            { node with
                CompDecl.Fields = field::node.Fields
            }
        member node.addFields (fields:FieldDecl list) =
            { node with
                CompDecl.Fields = fields@node.Fields
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
        member node.removeProvPorts (provPorts:ProvPortDecl list) =
            let provPortsSet = provPorts |> Set.ofList
            { node with
                CompDecl.ProvPorts = (node.ProvPorts |> List.filter (fun _provPort -> (provPortsSet.Contains _provPort) = false));
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
            // Only works, if binding was declared in current node.
            // If binding might also be declared in the parent node, maybe
            // the function tryFindProvPortOfReqPort is what you want.
            node.Bindings |> List.find (fun bndg -> bndg.Target.ReqPort=reqPort && bndg.Target.Comp=None)
            
        member node.removeStep (step:StepDecl) =
            { node with
                CompDecl.Steps = (node.Steps |> List.filter (fun _step -> _step<>step));
            }
        member node.removeSteps (steps:StepDecl list) =
            let stepsSet = steps |> Set.ofList
            { node with
                CompDecl.Steps = (node.Steps |> List.filter (fun _step -> (stepsSet.Contains _step) = false));
            }
        member node.addStep (step:StepDecl) =
            { node with
                CompDecl.Steps = step::node.Steps
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
        // TODO: Move to rewriter
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
        
        // search in the model        
        member model.tryFindBindingOfReqPort (pathOfReqPort:ReqPortPath) : BndDeclPath option =
            // option, because it might not be in the model (binding is not declared, or declared in the parent node
            // of "model"
            let compPath,reqPort = pathOfReqPort
            let node = model.getDescendantUsingPath compPath
            // Try to find the binding in node
            let binding =
                node.Bindings |> List.tryFind (fun bndg -> bndg.Target.ReqPort=reqPort && bndg.Target.Comp=None)
            match binding with
                | Some (binding) ->
                    // case 1: Binding found in the node
                    Some (compPath,binding)
                | None ->                    
                    // Try to find binding in the parent of node
                    if compPath = [] then
                        // case 2: the binding was not declared in the model or model is not the real root component. We
                        //         cannot search in the parent of node
                        None
                    else
                        let parentPath = compPath.Tail
                        let parentNode = model.getDescendantUsingPath parentPath                        
                        let binding =
                            node.Bindings |> List.tryFind (fun bndg -> bndg.Target.ReqPort=reqPort && bndg.Target.Comp=Some(compPath.Head))
                        match binding with
                            | Some (binding) ->
                                // case 3: Binding found in the parent
                                Some (parentPath,binding)
                            | None ->
                                // case 4: Binding not found in the parent, and not found in the node itself
                                None
                
        member model.tryGetProvPort (bndDeclPath:BndDeclPath) : ProvPortPath option = //TODO: option useful? where is it used?
            let compPath,bndDecl = bndDeclPath
            let node = model.getDescendantUsingPath compPath
            if bndDecl.Source.Comp=None then
                Some (compPath,bndDecl.Source.ProvPort)
            else
                Some (bndDecl.Source.Comp.Value::compPath,bndDecl.Source.ProvPort)

        member model.collectDelayedProvPorts : ProvPortPath list =
            let rec collectDelayedProvPortsInSub (path:CompPath) (compDecl:CompDecl) =
                let subs = compDecl.Subs |> List.collect (fun compDecl -> collectDelayedProvPortsInSub (compDecl.Comp::path) compDecl  )
                let local =
                    compDecl.Bindings |> List.filter (fun bndDecl -> bndDecl.Kind = BndKind.Delayed) // now only delayed bindings
                                      |> List.map (fun bndDecl -> (path,bndDecl)) // now we have got the bindings with path
                                      |> List.map (model.tryGetProvPort) // now we have got the prov ports
                                      |> List.filter (fun provPortOpt -> provPortOpt.IsSome) // filter out entries, where the target port was not found
                                      |> List.map (fun provPortOpt -> provPortOpt.Value) // exactly what we want
                local@subs
            let compPath= [model.Comp]
            collectDelayedProvPortsInSub compPath model
    
    // Extension methods    
    type Expr with
        static member createOredExpr (exprs:Expr list) : Expr =
            if exprs.IsEmpty then
                Expr.Literal(Val.BoolVal(false)) //see Conjunctive Normal Form. An empty clause is unsatisfiable
            else if exprs.Tail = [] then
                // only one element, so return it
                exprs.Head
            else
                Expr.BExpr(exprs.Head,BOp.Or,Expr.createOredExpr exprs.Tail)
        static member createAndedExpr (exprs:Expr list) : Expr =
            if exprs.IsEmpty then
                Expr.Literal(Val.BoolVal(true)) //see Conjunctive Normal Form. If there is no clause, the formula is true.
            else if exprs.Tail = [] then
                // only one element, so return it
                exprs.Head
            else
                Expr.BExpr(exprs.Head,BOp.And,Expr.createAndedExpr exprs.Tail)

                
    // some local helpers
    let rec rewriteFaultExpr (faultMap:Map<Fault,Fault>) (faultExpr:FaultExpr) = //from->to
        let rewriteFault (fault) : Fault =
            if faultMap.ContainsKey fault then
                faultMap.Item fault
            else
                fault
        match faultExpr with
            | FaultExpr.Fault (fault) -> FaultExpr.Fault (rewriteFault fault)
            | FaultExpr.NotFault (faultExpr) -> FaultExpr.NotFault(rewriteFaultExpr faultMap faultExpr)
            | FaultExpr.AndFault (left,right) -> FaultExpr.AndFault (rewriteFaultExpr faultMap left, rewriteFaultExpr faultMap right)
            | FaultExpr.OrFault (left,right) -> FaultExpr.OrFault (rewriteFaultExpr faultMap left, rewriteFaultExpr faultMap right)

    let rewriteFaultExprOption (faultMap:Map<Fault,Fault>) (faultExpr:FaultExpr option) =
        match faultExpr with
            | None -> None
            | Some (faultExpr) -> Some (rewriteFaultExpr faultMap faultExpr)

    let itemOrOld<'a when 'a:comparison> (map:Map<'a,'a>) (item:'a) : 'a  =
        if map.ContainsKey item then
            map.Item item
        else
            item
                    
    let rec rewriteExpr (varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (expr:Expr) : Expr=
        match expr with
            | Expr.Literal (_val) -> Expr.Literal(_val)
            | Expr.ReadVar (_var) ->
                let newVar = itemOrOld varMap _var
                Expr.ReadVar (newVar)
            | Expr.ReadField (field) ->
                let newField = itemOrOld fieldMap field
                Expr.ReadField (newField)
            | Expr.UExpr (expr,uop) -> Expr.UExpr(rewriteExpr (varMap,fieldMap) expr,uop)
            | Expr.BExpr (left, bop, right) -> Expr.BExpr(rewriteExpr (varMap,fieldMap) left,bop,rewriteExpr (varMap,fieldMap) right)

    let rewriteParam (varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (_param:Param) : Param =
        match _param with
            | Param.ExprParam (expr) -> Param.ExprParam(rewriteExpr (varMap,fieldMap) expr)
            | Param.InOutVarParam (var) ->
                let newVar = itemOrOld varMap var
                Param.InOutVarParam (newVar)
            | Param.InOutFieldParam (field) ->                    
                let newField = itemOrOld fieldMap (field)
                Param.InOutFieldParam (newField)

    let rec rewriteStm (reqPortMap:Map<ReqPort,ReqPort>,faultMap:Map<Fault,Fault>,varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (stm:Stm) : Stm =
        match stm with
            | Stm.AssignVar (var,expr) ->
                let newExpr = rewriteExpr (varMap,fieldMap) expr
                let newVar = itemOrOld varMap var
                Stm.AssignVar (newVar, newExpr)
            | Stm.AssignField (field, expr) ->
                let newField = itemOrOld fieldMap (field)
                let newExpr = rewriteExpr (varMap,fieldMap) expr
                Stm.AssignField (newField, newExpr)
            | Stm.AssignFault (fault, expr) ->
                let newFault = itemOrOld faultMap (fault)
                let newExpr = rewriteExpr (varMap,fieldMap)  expr
                Stm.AssignFault (newFault, newExpr)
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.map (rewriteStm (reqPortMap,faultMap,varMap,fieldMap))
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (rewriteExpr (varMap,fieldMap)  expr,rewriteStm (reqPortMap,faultMap,varMap,fieldMap) stm) )
                Stm.Choice(newChoices)
            | Stm.CallPort (reqPort,_params) ->
                let newReqPort = itemOrOld reqPortMap (reqPort)
                let newParams = _params |> List.map (rewriteParam (varMap,fieldMap) )
                Stm.CallPort (newReqPort,newParams)
            | Stm.StepComp (comp) ->
                Stm.StepComp (comp)
            | Stm.StepFault (fault) ->
                let newFault = itemOrOld faultMap (fault)
                Stm.StepFault (newFault)
                
    let rewriteBehavior (reqPortMap:Map<ReqPort,ReqPort>,faultMap:Map<Fault,Fault>,varMap:Map<Var,Var>,fieldMap:Map<Field,Field>) (behavior:BehaviorDecl) =
        let newLocals =
            behavior.Locals |> List.map (fun varDecl -> {varDecl with VarDecl.Var = itemOrOld varMap varDecl.Var})
        {
            BehaviorDecl.Locals= newLocals;
            BehaviorDecl.Body = rewriteStm (reqPortMap,faultMap,varMap,fieldMap) behavior.Body;
        }
    let prependStmBeforeStm (stm:Stm) (oldStm:Stm) =
        match oldStm with
            | Stm.Block (stmnts) -> Stm.Block (stm::stmnts) //prepend statement to existing Block
            | _ -> Stm.Block (stm::oldStm::[]) //create a new Block with stm as first entry


    let rewriteStm_onlyVars (varMap:Map<Var,Var>) =
        rewriteStm (Map.empty<ReqPort,ReqPort>,Map.empty<Fault,Fault>,varMap,Map.empty<Field,Field>)
    
    
    let rec rewriteExpr_varsToFields (varMap:Map<Var,Field>) (expr:Expr) : Expr=
        match expr with
            | Expr.Literal (_val) -> Expr.Literal(_val)
            | Expr.ReadVar (_var) ->
                if varMap.ContainsKey _var then
                    Expr.ReadField(varMap.Item _var)
                else
                    Expr.ReadVar (_var)
            | Expr.ReadField (field) -> Expr.ReadField (field)
            | Expr.UExpr (expr,uop) -> Expr.UExpr(rewriteExpr_varsToFields (varMap) expr,uop)
            | Expr.BExpr (left, bop, right) -> Expr.BExpr(rewriteExpr_varsToFields (varMap) left,bop,rewriteExpr_varsToFields (varMap) right)
            
    let rewriteParam_varsToFields (varMap:Map<Var,Field>) (_param:Param) : Param =
        match _param with
            | Param.ExprParam (expr) -> Param.ExprParam(rewriteExpr_varsToFields (varMap) expr)
            | Param.InOutVarParam (var) ->
                if varMap.ContainsKey var then
                    Param.InOutFieldParam (varMap.Item var)
                else
                    Param.InOutVarParam (var)
            | Param.InOutFieldParam (field) -> 
                Param.InOutFieldParam (field)

    let rec rewriteStm_varsToFields (varMap:Map<Var,Field>) (stm:Stm) : Stm =
        match stm with
            | Stm.AssignVar (var,expr) ->
                let newExpr = rewriteExpr_varsToFields (varMap) expr                
                if varMap.ContainsKey var then              
                    Stm.AssignField (varMap.Item var, newExpr)
                else
                    Stm.AssignVar (var, newExpr)                
            | Stm.AssignField (field, expr) ->
                Stm.AssignField (field, expr)
            | Stm.AssignFault (fault, expr) ->
                Stm.AssignFault (fault, expr)
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.map (rewriteStm_varsToFields (varMap))
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (rewriteExpr_varsToFields (varMap)  expr,rewriteStm_varsToFields (varMap) stm) )
                Stm.Choice(newChoices)
            | Stm.CallPort (reqPort,_params) ->
                let newParams = _params |> List.map (rewriteParam_varsToFields (varMap) )
                Stm.CallPort (reqPort,newParams)
            | Stm.StepComp (comp) ->
                Stm.StepComp (comp)
            | Stm.StepFault (fault) ->
                Stm.StepFault (fault)
    



    let rec rewriteExpr_varsToExpr (varMap:Map<Var,Expr>) (expr:Expr) : Expr=
        match expr with
            | Expr.Literal (_val) -> Expr.Literal(_val)
            | Expr.ReadVar (_var) ->
                if varMap.ContainsKey _var then
                    varMap.Item _var
                else
                    Expr.ReadVar (_var)
            | Expr.ReadField (field) -> Expr.ReadField (field)
            | Expr.UExpr (expr,uop) -> Expr.UExpr(rewriteExpr_varsToExpr (varMap) expr,uop)
            | Expr.BExpr (left, bop, right) -> Expr.BExpr(rewriteExpr_varsToExpr (varMap) left,bop,rewriteExpr_varsToExpr (varMap) right)
            
    let rewriteParam_varsToExpr (varMap:Map<Var,Expr>) (_param:Param) : Param =
        match _param with
            | Param.ExprParam (expr) -> Param.ExprParam(rewriteExpr_varsToExpr (varMap) expr)
            | Param.InOutVarParam (var) ->
                if varMap.ContainsKey var then
                    failwith "BUG: ExprParam may never be used as InoutVarParam of another Call"
                else
                    Param.InOutVarParam (var)
            | Param.InOutFieldParam (field) -> 
                Param.InOutFieldParam (field)

    let rec rewriteStm_varsToExpr (varMap:Map<Var,Expr>) (stm:Stm) : Stm =
        match stm with
            | Stm.AssignVar (var,expr) ->
                let newExpr = rewriteExpr_varsToExpr (varMap) expr                
                if varMap.ContainsKey var then              
                    failwith "BUG: ExprParam may never be assigned to. Maybe in the model is a missing 'inout' in the parameter list of a reqCall (TODO: Move this into a consistency check)." // User tries to replace something like "localVar:=7+2" with "5+intField:=7+2"
                else
                    Stm.AssignVar (var, newExpr)                
            | Stm.AssignField (field, expr) ->
                Stm.AssignField (field, expr)
            | Stm.AssignFault (fault, expr) ->
                Stm.AssignFault (fault, expr)
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.map (rewriteStm_varsToExpr (varMap))
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (rewriteExpr_varsToExpr (varMap)  expr,rewriteStm_varsToExpr (varMap) stm) )
                Stm.Choice(newChoices)
            | Stm.CallPort (reqPort,_params) ->
                let newParams = _params |> List.map (rewriteParam_varsToExpr (varMap) )
                Stm.CallPort (reqPort,newParams)
            | Stm.StepComp (comp) ->
                Stm.StepComp (comp)
            | Stm.StepFault (fault) ->
                Stm.StepFault (fault)

                
    let rec rewriteStm_stepFaultToPortCall (faultMap:Map<Fault,ProvPort*ReqPort>) (stm:Stm) : Stm =
        match stm with
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.map (rewriteStm_stepFaultToPortCall faultMap)
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (expr,rewriteStm_stepFaultToPortCall faultMap stm) )
                Stm.Choice(newChoices)
            | Stm.StepFault (fault) ->
                let (_,artificialReqPort) = faultMap.Item fault
                Stm.CallPort (artificialReqPort,[])
            | _ -> stm

    let rec rewriteStm_assignFaultToAssignField (faultToConvert:Fault,field:Field) (stm:Stm) : Stm =
        match stm with
            | Stm.Block (smnts) ->
                let newStmnts = smnts |> List.map (rewriteStm_assignFaultToAssignField (faultToConvert,field))
                Stm.Block(newStmnts)
            | Stm.Choice (choices:(Expr * Stm) list) ->
                let newChoices = choices |> List.map (fun (expr,stm) -> (expr,rewriteStm_assignFaultToAssignField (faultToConvert,field) stm) )
                Stm.Choice(newChoices)
            | Stm.AssignFault (fault,expr) ->
                if faultToConvert = fault then
                    Stm.AssignField (field,expr)
                else
                    failwith "A fault value should only be assigned in the step of the fault (and in no other fault)"
            | _ -> stm
    

    ////////////////////////////////////////////////////////////////////////////
    
    // Statement walker
    
    type WalkerAtomarAssessor<'a> = (Stm*'a)->(bool*'a) // (statement,oldState) -> (keepOnWalking,newState)
    type WalkerReductionAssessor<'a> = (Stm -> 'a) -> Stm list -> 'a //assessor -> list of statements -> state

                
    // see ScmConsistencyCheck.fs for a usage example
    let rec stmTransitiveWalker<'a> (assessor:WalkerAtomarAssessor<'a>) (assessAndMergeStates:WalkerReductionAssessor<'a>) (neutralState:'a) (model:CompDecl)
                       (compPath:CompPath) (oldState:'a) (stm:Stm): 'a =
        
        // need the complete model, because a relevant binding might be declared in the parent node
        // Note: selectValue on empty list should return neutralValue (selectValue (fun stm -> 'a) [] = neutralValue:'a)

        let keepOnWalking,newState = assessor (stm,oldState)
        if keepOnWalking = false then
            newState
        else
            let walkMe = stmTransitiveWalker assessor assessAndMergeStates neutralState model // these parameters stay the same in the remainder, so use an abbrev.
            match stm with
                | Stm.Block (stmts) ->
                    stmts |> assessAndMergeStates (fun stm -> walkMe compPath newState stm)
                | Stm.Choice (choices:(Expr * Stm) list) ->
                    choices |> List.map (fun (guard,stm) -> stm )
                            |> assessAndMergeStates (fun stm -> walkMe compPath newState stm)                  
                | Stm.StepComp (comp) ->
                    let newPath = comp::compPath
                    let compDecl = model.getDescendantUsingPath newPath
                    compDecl.Steps |> List.map (fun step -> step.Behavior.Body )
                                   |> assessAndMergeStates (fun stm -> walkMe newPath newState stm)
                | Stm.StepFault (fault) ->
                    let compDecl = model.getDescendantUsingPath compPath
                    compDecl.Faults |> List.filter (fun faultDecl -> faultDecl.Fault = fault)
                                    |> List.map (fun fault -> fault.Step.Body)
                                    |> assessAndMergeStates (fun stm -> walkMe compPath newState stm)
                | Stm.CallPort (reqPort,_params) ->
                    let bndDeclPath = model.tryFindBindingOfReqPort (compPath,reqPort)
                    match bndDeclPath with
                        | None ->
                            // Binding could not be found: Model is incomplete. But: it is not because of (checker)
                            neutralState
                        | Some(bndDeclCompPath,binding) ->
                            let provPortPath = model.tryGetProvPort (bndDeclCompPath,binding)
                            match provPortPath with
                                | None ->
                                    neutralState  // Binding could not be found: Model is incomplete. But: it is not because of (checker)
                                | Some(provPortPath,provPort) ->
                                    let provPortCompDecl = model.getDescendantUsingPath provPortPath
                                    let provPortDecls = provPortCompDecl.getProvPortDecls(provPort)
                                    provPortDecls |> List.map (fun provPortDecl -> provPortDecl.Behavior.Body)
                                                  |> assessAndMergeStates (fun stm -> walkMe provPortPath newState stm)
                | _ ->
                     // Return calculated value, when no further walking is possible.
                     // This is used, when the assessor returns keepOnWalking=true, but the statement to examine
                     // is an assignment or something similar.
                    newState


                    
    [<RequireQualifiedAccess>]
    type BehaviorWithLocation = 
        | InProvPort of CompPath * ProvPortDecl * BehaviorDecl
        | InFault of CompPath * FaultDecl * BehaviorDecl
        | InStep of CompPath * StepDecl * BehaviorDecl
            with
                member beh.Behavior =
                    match beh with
                        | InProvPort (_,_,beh) -> beh
                        | InFault (_,_,beh) -> beh
                        | InStep (_,_,beh) -> beh
                member beh.Location =
                    match beh with
                        | InProvPort (path,_,_) -> path
                        | InFault (path,_,_) -> path
                        | InStep (path,_,_) -> path

                static member collectAllBehaviorsInPath (model:CompDecl) (compPath:CompPath) : BehaviorWithLocation list =
                    let compDecl = model.getDescendantUsingPath compPath
                    let provPorts =
                        compDecl.ProvPorts |> List.map (fun provPort -> BehaviorWithLocation.InProvPort(compPath,provPort,provPort.Behavior) )
                    let steps =
                        compDecl.Steps |> List.map (fun step -> BehaviorWithLocation.InStep(compPath,step,step.Behavior) )
                    let faults =
                        compDecl.Faults |> List.map (fun fault -> BehaviorWithLocation.InFault(compPath,fault,fault.Step) )
                    provPorts @ steps @ faults

                static member collectAllBehaviorsInModel (model:CompDecl) : BehaviorWithLocation list =
                    let rec collectBehaviorsInSub (path:CompPath) (compDecl:CompDecl) =
                        let subs = compDecl.Subs |> List.collect (fun compDecl -> collectBehaviorsInSub (compDecl.Comp::path) compDecl  )
                        let local = BehaviorWithLocation.collectAllBehaviorsInPath model path
                        local@subs
                    let compPath= [model.Comp]
                    collectBehaviorsInSub compPath model
                                    