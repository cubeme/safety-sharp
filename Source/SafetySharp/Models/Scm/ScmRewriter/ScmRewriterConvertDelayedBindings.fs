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

module internal ScmRewriterConvertDelayedBindings =
    open ScmHelpers
    open ScmRewriterBase
    
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
    
    
    let selectRootComponentForConvertingDelayedBindings : ScmRewriteFunction<unit> = scmRewrite {
        // Use As1
        let! state = getState
        if (state.ConvertDelayedBindings.IsSome) then
            return ()
        else
            let rootComp = state.Model
            let rootPath = [state.Model.Comp]
            let convertDelayedBindingsState = ()
            let modifiedState =
                { state with
                    ScmRewriteState.ChangingSubComponent = rootComp;
                    ScmRewriteState.PathOfChangingSubcomponent = rootPath;
                    ScmRewriteState.ConvertDelayedBindings = Some(convertDelayedBindingsState);
                    ScmRewriteState.Tainted = true;
                }
            return! putState modifiedState
    }


    let createArtificialFieldsForProvPort (fieldNamePrefix:string) (bndDecl:BndDecl) (provPortDecl:ProvPortDecl)
                : ScmRewriteFunction<(VarDecl*Field) list> = scmRewrite {
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
        do! updateSubComponentToChange oldCompDecl        
        return  varDeclToFieldList
    }

    let createPreStepOfProvPort (fieldNamePrefix:string)  (provPortDecl:ProvPortDecl) : ScmRewriteFunction<unit> = scmRewrite {
        let varListOfBeh = provPortDecl.Behavior.Locals |> List.map (fun param -> param.Var )
        let newVarNamesOfBehBasedOn = varListOfBeh |> List.map (fun var -> sprintf "preStepVar_%s_%s" fieldNamePrefix var.getName)
        let! newVarsForBeh = getUnusedVarNames newVarNamesOfBehBasedOn
        
        // replace localVars (use rewriteBehavior, because also the BehaviorDecl.Locals get exchanged)
        let newBehavior1 = rewriteBehavior (Map.empty,Map.empty,varMap,Map.empty) provPortDecl.Behavior

        // replace outs in param with fields
        //rewriteStm_varsToFields (varMap:Map<Var,Field>) (stm:Stm) : Stm =

        // add localVars to Step
        // add stm to Step
        //prependStmBeforeStm
        return ()
    }
    
    let createReflectionOfProvPort (provPortDecl:ProvPortDecl) : ScmRewriteFunction<unit> = scmRewrite {        
        let newProvPort = getUnusedProvPortName (sprintf "%s_delayed" provPortDecl.getName)
        return ()
        //a
    }

    let replaceDelayedBinding (bndDecl:BndDecl) : ScmRewriteFunction<unit> = scmRewrite {
        return ()
        //a
    }

    let findProvPortOfDelayedBinding (bndDecl:BndDecl) : ScmRewriteFunction<ProvPortDecl> = scmRewrite {
        let! state = getState
        // Use As1
        let location = state.PathOfChangingSubcomponent
        let locProvPort = state.ChangingSubComponent.tryGetProvPort (location,bndDecl)        
        //Assume, that binding is correct
        let provPortComp,provPort = locProvPort.Value
       // Use As2: Assume provPortComp=location
        let provPortDecls = state.ChangingSubComponent.getProvPortDecls provPort
        // Use As3
        let provPortDecl = provPortDecls.Head                
        return provPortDecl
    }


    let convertDelayedBinding : ScmRewriteFunction<unit> = scmRewrite {
        let! state = getState
        let bindingToConvert =
            // Use As2
            state.ChangingSubComponent.Bindings |> List.tryFind (fun bndDecl -> bndDecl.Kind = BndKind.Delayed)
        match bindingToConvert with
            | None ->
                // nothing to do, work is finished
                return ()
            | Some(bindingToConvert) ->
                let! provPortDecl = findProvPortOfDelayedBinding bindingToConvert
                let! newProvPort = getUnusedProvPortName (sprintf "%s_delayed" provPortDecl.getName)
                let newNamePrefix = newProvPort.getName
                let! varDeclToNewFieldList = createArtificialFieldsForProvPort newNamePrefix bindingToConvert provPortDecl
                // fields have been created
                do! createPreStepOfProvPort newNamePrefix provPortDecl
                do! createReflectionOfProvPort provPortDecl
                do! replaceDelayedBinding bindingToConvert
                return ()
    }
    
    
    let convertDelayedBindingsWriteBackChangesIntoModel  : ScmRewriteFunction<unit> = scmRewrite {
        // Use As1
        let! state = getState
        if (state.ConvertDelayedBindings.IsNone) then
            return ()
        else
            let! compDecl = getSubComponentToChange
            let convertDelayedBindingsState = state.ConvertDelayedBindings.Value
            let newModel = state.Model.replaceDescendant state.PathOfChangingSubcomponent compDecl
            let modifiedState =
                { state with
                    ScmRewriteState.ChangingSubComponent = newModel;
                    ScmRewriteState.PathOfChangingSubcomponent = [newModel.Comp];
                    ScmRewriteState.Model = newModel;
                    ScmRewriteState.ConvertDelayedBindings = None;
                    ScmRewriteState.Tainted = true; // if tainted, set tainted to true
                }
            return! putState modifiedState
    }

    let convertDelayedBindings : ScmRewriteFunction<unit> = scmRewrite {        
        do! selectRootComponentForConvertingDelayedBindings
        do! (iterateToFixpoint convertDelayedBinding)
        do! convertDelayedBindingsWriteBackChangesIntoModel
    }
