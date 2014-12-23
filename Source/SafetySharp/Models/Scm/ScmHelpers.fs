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
        
        member node.getCompletlyFreshName (basedOn:string) : string =
            // TODO: Buffering: Add a Set, which contains all names. This function can be altered to collect all names
            let existsName name : bool =
                let existsInFields = node.Fields |> List.exists (fun field -> field.getName = name)
                let existsInFaults =
                    let existsInFault (fault:FaultDecl) =
                        let existsAsLocalVar = fault.Step.Locals |> List.exists (fun var -> var.getName = name)
                        let isNameOfFault = fault.getName = name
                        isNameOfFault || existsAsLocalVar
                    node.Faults |> List.exists existsInFault
                let existsInReqPorts = node.ReqPorts |> List.exists (fun reqPort -> reqPort.getName = name)
                let existsInProvPorts =
                    let existsInProvPort (provPort:ProvPortDecl) : bool =
                        let existsAsParameter = provPort.Params |> List.exists (fun param -> param.getName = name)
                        let existsAsLocalVar = provPort.Behavior.Locals |> List.exists (fun var -> var.getName = name)
                        let isNameOfPort = provPort.getName = name
                        isNameOfPort || existsAsParameter || existsAsLocalVar
                    node.ProvPorts |> List.exists existsInProvPort
                let existsInSteps =
                    let existsInStep (step:StepDecl) =
                        let existsAsLocalVar = step.Behavior.Locals |> List.exists (fun var -> var.getName = name)
                        existsAsLocalVar
                    node.Steps |> List.exists existsInStep
                existsInFields || existsInFaults  || existsInReqPorts || existsInProvPorts || existsInSteps
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
        member node.getUnusedFieldName (basedOn:string) : Field =
            Field(node.getCompletlyFreshName basedOn)
                                
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
        member node.getUnusedFaultName (basedOn:string) : Fault =
            Fault.Fault(node.getCompletlyFreshName basedOn)

        member node.removeReqPort (reqPort:ReqPortDecl) =
            { node with
                CompDecl.ReqPorts = (node.ReqPorts |> List.filter (fun _reqPort -> reqPort<>_reqPort));
            }
        member node.addReqPort (reqPort:ReqPortDecl) =
            { node with
                CompDecl.ReqPorts = reqPort::node.ReqPorts
            }
        member node.getUnusedReqPortName (basedOn:string) : ReqPort =
            ReqPort(node.getCompletlyFreshName basedOn)
                
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
        member node.getUnusedProvPortName (basedOn:string) : ProvPort =
            ProvPort(node.getCompletlyFreshName basedOn)
                
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
