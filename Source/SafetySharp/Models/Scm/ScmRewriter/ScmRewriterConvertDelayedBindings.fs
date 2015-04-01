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

module internal ScmRewriterConvertDelayedBindings =
    open ScmHelpers
    open ScmRewriterBase
    open SafetySharp.Workflow
    open ScmWorkflow
    
    // Assumptions:
    //  As1: Only root component gets converted
    //  As2: Everything is leveled up
    //  As3: No fault exists (converted before)


    // Idea:
    //   For each delayed binding:
    //     * Check if prov port does not write to a field
    //     * Check that there is no read-Operation on a inout-Parameter/in-Parameter
    //     * Introduce new fields for each inout-Parameter written to
    //     * At the end of _all_ steps  ("Post-Step"), add Call to ProvPort with new artificial parameters
    //     * Remove/Replace the Delayed Binding by an instantaneous.
    //     * Replace the Port Call by a BlockStatement, where each of the inout-Parameter gets assigned to the new Field
    //   Note:
    //     * The ProvPort call may contain a choice. Thus, the content of the artificial fields may not always be
    //       simply an expression depending on pre-Values of Fields. (Example: Guards true/true;
    //       Statements: "field1:=1;field2:=1"/"field1:=2;field2:=2" TODO: Create example file
    //     * Only for the step of the root-component we can guarantee, that nothing happens before the first statement
    //       and nothing after the last. 
    //     * "Post-Step" must be executed after the step of the root. It is not enough to add it as postfix to all local
    //       steps, because the local step may be executed later by the root step and the environment has been changed before.
    //       See examples callDelayedCaution1.scm and callDelayedCaution2.scm.
    //       (making a "Pre-Step" does not resolve the problem. It cannot be assured that it will be executed always
    //       after the root step. Later it might make a difference, if we use a Pre-Step or Post-Step, when time
    //       is added, which is increased automatically after a step.)
    //     * But: We could save the artificial fields in a list. It could give hints for later optimizations.
    //       We make a PreStep: Thus the values of the fields corresspond to the indeterministic initialisation
    //       (Example: intField1 : int = 1,2; intField2 : int =5,6; DelayedPort with (intField1+intField2) returns
    //       the correct value)
    //     * Later: Increasing the values of clocks need also to be included into the Pre-Step/Post-Step.
    //   TODO:
    //     * When are execution in the "Post-Step" (Note 2) and execution as last statements of a step the same???
    //     * Difference between making it "Pre-Step" or "Post-Step" (with declared output-values of the step before the
    //       First Step)
    //     * Create example with indeterministic initialisazion
    
    type ScmRewriterConvertDelayedBindingsState = {
        Model : ScmModel;
        PathOfChangingSubcomponent : CompPath; //path of the Parent of the subcomponent, which gets changed
        TakenNames : Set<string>;
    }
        with
            interface IScmModel<ScmRewriterConvertDelayedBindingsState> with
                member this.getModel : ScmModel = this.Model
                member this.setModel (model:ScmModel) =
                    { this with
                        ScmRewriterConvertDelayedBindingsState.Model = model
                    }
            interface IScmChangeSubcomponent<ScmRewriterConvertDelayedBindingsState> with
                member this.getPathOfChangingSubcomponent = this.PathOfChangingSubcomponent
                member this.setPathOfChangingSubcomponent (compPath:CompPath) =
                    { this with
                        ScmRewriterConvertDelayedBindingsState.PathOfChangingSubcomponent = compPath
                    }
            interface IFreshNameDepot<ScmRewriterConvertDelayedBindingsState> with
                member this.getTakenNames : Set<string> = this.TakenNames
                member this.setTakenNames (takenNames:Set<string>) =
                    { this with
                        ScmRewriterConvertDelayedBindingsState.TakenNames = takenNames
                    }
    
    type ScmRewriterConvertDelayedBindingsFunction<'returnType> = WorkflowFunction<ScmRewriterConvertDelayedBindingsState,ScmRewriterConvertDelayedBindingsState,'returnType>
    type ScmRewriterConvertDelayedBindingsWorkflowState = WorkflowState<ScmRewriterConvertDelayedBindingsState>
    
    let createArtificialFieldsForProvPort (fieldNamePrefix:string) (bndDecl:BndDecl) (provPortDecl:ProvPortDecl)
                : ScmRewriterConvertDelayedBindingsFunction<Map<Var,Field>> = workflow {
        let varList = provPortDecl.Params |> List.map (fun param -> param.Var )
        let fieldNamesBasedOn = varList |> List.map (fun var -> sprintf "%s_%s" fieldNamePrefix var.getName)
        let! newFieldList = getUnusedFieldNames fieldNamesBasedOn
        let varDeclToFieldList = List.zip varList newFieldList
        let newFieldDecls =            
            let createField (varDecl:VarDecl,field) =
                {
                    FieldDecl.Field = field;
                    FieldDecl.Type = varDecl.Type;
                    FieldDecl.Init = [varDecl.Type.getDefaultInitVal];
                }
            varDeclToFieldList |> List.map (fun entry -> createField entry)
        let! oldCompDecl = getSubComponentToChange
        let newCompDecl = oldCompDecl.addFields newFieldDecls        
        do! updateSubComponentToChange newCompDecl        
        let varToFieldMap = varDeclToFieldList |> List.map (fun (varDecl,field) -> varDecl.Var,field) |> Map.ofList
        return  varToFieldMap
    }

    let createPreStepOfProvPort (fieldNamePrefix:string)  (provPortDecl:ProvPortDecl) (varToNewFieldMap:Map<Var,Field>) : ScmRewriterConvertDelayedBindingsFunction<unit> = workflow {
        let varListOfBeh = provPortDecl.Behavior.Locals |> List.map (fun param -> param.Var )
        let newVarNamesOfBehBasedOn = varListOfBeh |> List.map (fun var -> sprintf "preStepVar_%s_%s" fieldNamePrefix var.getName)
        let! newVarsForBeh = getUnusedVarNames newVarNamesOfBehBasedOn
        
        // replace localVars in ProvPortDecl (use rewriteBehavior, because also the BehaviorDecl.Locals get exchanged)
        let varMapLocals = List.zip varListOfBeh newVarsForBeh |> Map.ofList
        let newBehavior1 = rewriteBehavior (Map.empty,Map.empty,varMapLocals,Map.empty) provPortDecl.Behavior
        

        // replace outs in param with fields
        let newBehavior2 =
            {
                BehaviorDecl.Locals = newBehavior1.Locals;
                BehaviorDecl.Body = rewriteStm_varsToFields varToNewFieldMap newBehavior1.Body;
            }

        // add prepend modified ProvPortDecl to Step
        let! compDecl = getSubComponentToChange
        // use As3
        let step = compDecl.Steps.Head
        let newBehavior3 =
            {
                BehaviorDecl.Locals = newBehavior2.Locals @step.Behavior.Locals; // add vars to Step
                BehaviorDecl.Body = prependStmBeforeStm newBehavior2.Body step.Behavior.Body; //prepend new Stm before step
            }
        let newStep =
            { step with
                StepDecl.Behavior = newBehavior3;
            }
        let newCompDecl = compDecl.replaceStep(step,newStep)
        do! updateSubComponentToChange newCompDecl
        return ()
    }
    
    let createReflectionOfProvPort (oldProvPortDecl:ProvPortDecl) (varToNewFieldMap:Map<Var,Field>) (newProvPort:ProvPort) : ScmRewriterConvertDelayedBindingsFunction<unit> = workflow {        
        let assignments =
            varToNewFieldMap |> Map.toList
                             |> List.map (fun (var,field)-> Stm.AssignVar(var,Expr.ReadField(field)))
        let newStep = Stm.Block (assignments)
        let newBehavior =
            { 
                BehaviorDecl.Locals = oldProvPortDecl.Behavior.Locals;
                BehaviorDecl.Body = newStep;
            }
        let newProvPort =
            { oldProvPortDecl with
                ProvPortDecl.ProvPort = newProvPort;
                ProvPortDecl.Behavior = newBehavior;
            }
        
        let! compDecl = getSubComponentToChange
        let newCompDecl = compDecl.addProvPort(newProvPort) //Note: Only add and not replace! The old ProvPort might be necessary for other instant calls
        do! updateSubComponentToChange newCompDecl

        return ()
    }

    let replaceDelayedBinding (bndDecl:BndDecl) (newProvPort:ProvPort) : ScmRewriterConvertDelayedBindingsFunction<unit> = workflow {
        let! compDecl = getSubComponentToChange
        let newBndSource =
            {
                BndSrc.Comp = [];
                BndSrc.ProvPort = newProvPort;
            }
        let newInstantBinding =
            {
                BndDecl.Kind = BndKind.Instantaneous;
                BndDecl.Source = newBndSource;
                BndDecl.Target = bndDecl.Target;
            }
        let newCompDecl = compDecl.replaceBinding(bndDecl,newInstantBinding)
        do! updateSubComponentToChange newCompDecl
        return ()
    }

    let findProvPortOfDelayedBinding (bndDecl:BndDecl) : ScmRewriterConvertDelayedBindingsFunction<ProvPortDecl> = workflow {
        let! state = getState
        // Use As1
        let location = state.PathOfChangingSubcomponent
        let! changingSubComponent = getSubComponentToChange
        let provPortComp,provPort = changingSubComponent.getProvPort (location,bndDecl)
       // Use As2: Assume provPortComp=location
        let provPortDecls = changingSubComponent.getProvPortDecls provPort
        // Use As3
        let provPortDecl = provPortDecls.Head                
        return provPortDecl
    }
        
    let convertDelayedBinding : ScmRewriterConvertDelayedBindingsFunction<unit> = workflow {
        let! state = getState
        let! changingSubComponent = getSubComponentToChange
        let bindingToConvert =
            // Use As2
            changingSubComponent.Bindings |> List.tryFind (fun bndDecl -> bndDecl.Kind = BndKind.Delayed)
        match bindingToConvert with
            | None ->
                // nothing to do, work is finished
                return ()
            | Some(bindingToConvert) ->
                let! provPortDecl = findProvPortOfDelayedBinding bindingToConvert
                let! newProvPort = getUnusedProvPortName (sprintf "%s_delayed" provPortDecl.getName)
                let newNamePrefix = newProvPort.getName
                let! varToNewFieldMap = createArtificialFieldsForProvPort newNamePrefix bindingToConvert provPortDecl
                // fields have been created
                do! createPreStepOfProvPort newNamePrefix provPortDecl varToNewFieldMap
                do! createReflectionOfProvPort provPortDecl varToNewFieldMap newProvPort
                do! replaceDelayedBinding bindingToConvert newProvPort
                return ()
    }
    
    let selectRootComponentForConvertingDelayedBindings<'oldState when 'oldState :> IScmModel<'oldState>> :
                        WorkflowFunction<'oldState,ScmRewriterConvertDelayedBindingsState,unit> = workflow {
        // Use As1
        let! model = getIscmModel
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let newState =
            {
                ScmRewriterConvertDelayedBindingsState.Model = model;
                ScmRewriterConvertDelayedBindingsState.PathOfChangingSubcomponent = [rootComp.Comp];
                ScmRewriterConvertDelayedBindingsState.TakenNames = rootComp.getTakenNames () |> Set.ofList;
            }
        do! updateState newState
    }
        
    let convertDelayedBindings : ScmRewriterConvertDelayedBindingsFunction<unit> = workflow {
        do! (iterateToFixpoint convertDelayedBinding)
    }

    let convertDelayedBindingsWrapper<'oldState when 'oldState :> IScmModel<'oldState>> :
                        WorkflowFunction<'oldState,ScmRewriterConvertDelayedBindingsState,unit> = workflow {
        do! selectRootComponentForConvertingDelayedBindings
        do! convertDelayedBindings
    }

