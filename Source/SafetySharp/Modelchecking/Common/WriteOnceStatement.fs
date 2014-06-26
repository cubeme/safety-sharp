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

namespace SafetySharp.Modelchecking.NuXmv


open SafetySharp.Modelchecking

type WriteOnceExpression = SimpleExpression
type WriteOnceGlobalField = SimpleGlobalField

type WriteOncePossibleEffect = {
    TakenDecisions : WriteOnceExpression list;
    TargetEffect : WriteOnceExpression;
} with 
    member this.getTakenDecisionsAsCondition: WriteOnceExpression =
        if this.TakenDecisions.IsEmpty then
            WriteOnceExpression.ConstLiteral(SimpleConstLiteral.BooleanLiteral(true))
        else
            // Concat every element with a logical and
            this.TakenDecisions.Tail |> List.fold (fun acc elem -> WriteOnceExpression.BinaryExpression(elem,MMBinaryOperator.LogicalAnd,acc)) this.TakenDecisions.Head

// A WriteOnceStatement is always an assignment


// Be cautious:
// in NuXmv "next(x):= case option1..., option2... esac": If guard of option1 is true, option2 is not taken. The guard of option2 is
// implicitly "not guard of option1 AND guard of option2". But sometimes we do not want this behavior. We want
// guardOfOption1 AND guardOfOption2 AND guardOfOption3 : {effectOfOption1,effectOfOption2,effectOfOption3}
// Thus we introduce the two different interpretations and conversions between them
type WriteOnceStatement = 
    | WriteOnceStatementEvaluateDecisionsParallel of Target : (WriteOnceGlobalField) * PossibleEffects : (WriteOncePossibleEffect list)
    | WriteOnceStatementEvaluateDecisionsSequential of Target : (WriteOnceGlobalField) * PossibleEffects : (WriteOncePossibleEffect list)
 with
    member this.getTarget =
        match this with
            | WriteOnceStatementEvaluateDecisionsParallel(target,_) -> target
            | WriteOnceStatementEvaluateDecisionsSequential(target,_) -> target

    member this.getPossibleEffectsForSequentialEvaluation =
        match this with
            | WriteOnceStatementEvaluateDecisionsParallel(_,possibleEffects) -> failwith "NotImplementedYet"
            | WriteOnceStatementEvaluateDecisionsSequential(_,possibleEffects) -> possibleEffects


// contains information, which Decicions have already been taken in the current statement
// - if an assignment is done, write it to a new variable (an artificial field), if it is not the last assignment to this variable
// - keep track, "SimpleGlobalField name" -> "SimpleGlobalField artificial/current"
// first implementation:
// - really unoptimized: each time a variable is written to, a new artifical variable is instanced with the assignment
// - keep state in a WriteOnceTypeArtificialCacheType with functions "setAssignment" "popDecision" "pushDecision" "getCurrentAssignment"
// - after everything is done, make a "next(state of actual x)=next(last artificial x belonging to actual x)"
// optimizations:
// - 1. recursively: when afterwards a variable is not read/written, throw it out
// - 2. maybe use idea of students in a thesis. Pool of ideas: Compiler
// - 3. different algorithm on basis of wp-calculus
// - 4. use simplifier of z3 (also appliable on result of 3)
// - 5. try to use many defines in model checker or exculde artificial fields from state

// One cache is valid for one sequence. Thus if a partition should be transformed, keep in mind, that its update
// needs to be transformed with one cache. Otherwise the bindings or the updates work on outdated data (the
// current value of a binding might depend on the result of an update)

// Current problem: SimpleExpressions also need to be rewritten. Expressions also need to be able to refer to artificial fields.
// - Solution 1: Introduce artifical fields in Simplified Metamodel, refactor SimpleExpression and SimpleStatement. WriteOnceStatement/Metamodel is only a restricted version of Statement. Simplified Metamodel could introduce a check "IsWriteOnce" and contain a "ToWriteOnce"-Member
// - Solution 2: Let WriteOnceType be something on its own. A field could be Artificial

// TODO: Refactor: readonly-parts as "let" and "Initialize" as only constructor
// TODO: include in name something like "Branch" or Decisions
type WriteOnceTypeFieldManager = {
    // static across a model
    SimpleFieldToInitialFieldMapping : Map<SimpleGlobalFieldWithContext,SimpleGlobalField list>; //map to the initial SimpleGlobalField
    // static across a scope. Changes with scopes. Organised as stacks. The head elements are the current elements. on a popScope the head elements are just thrown away
    SimpleFieldToCurrentArtificialFieldMapping : (Map<SimpleGlobalFieldWithContext,SimpleGlobalField>) list; //if an artificial field for a reference field is created, link the artificial fields to the field it overwrites
    SimpleFieldToNewArtificialFieldMapping : (Map<SimpleGlobalFieldWithContext,SimpleGlobalField>) list; //same as above, but only the fields introduced in this of the current scope. If a field is not "overwritten" in this scope, the map does not contain it.
    CurrentDecisions : (SimpleExpression list); //A Stack will all Decisions taken to this Branch
    //TODO: Move CurrentDecisions here
    // Following items are shared across all managers with the same .Initialize. They should only be changed internally.
    SimpleFieldToArtificialCounterShared : Map<SimpleGlobalFieldWithContext,int> ref; //every time a new artificial field is created, counter is increased. It is "ref" so its value is shared across different instances leading back to the same .Initialize
    CreatedArtificialFieldsShared : (SimpleGlobalField list) ref; //every time a new artificial field is created by the manager, it is associated with this manager. It is "ref" so its value is shared across different instances leading back to the same .Initialize

} with
    static member Initialize (fieldsOfPartition:SimpleGlobalField list) =
        let initializeCurrentValueMap  : Map<SimpleGlobalFieldWithContext,SimpleGlobalField>=
            let createEntry (fieldOfPartition:SimpleGlobalField) : (SimpleGlobalFieldWithContext*SimpleGlobalField) =
                ""
            fieldsOfPartition |> List.map createEntry
                              |> Map.ofList
        {
            WriteOnceTypeFieldManager.CurrentMapping = ref initializeCurrentValueMap
        }
    member this.pushScope (newDecision:SimpleExpression) : WriteOnceTypeFieldManager =
        let emptyNewMapping = Map.empty<SimpleGlobalFieldWithContext,SimpleGlobalField>
        let currentlyKnownMapping = this.SimpleFieldToCurrentArtificialFieldMapping.Head
        let newScope = 
            { this with
                SimpleFieldToCurrentArtificialFieldMapping = currentlyKnownMapping::this.SimpleFieldToCurrentArtificialFieldMapping;
                SimpleFieldToNewArtificialFieldMapping = emptyNewMapping::this.SimpleFieldToNewArtificialFieldMapping;
                CurrentDecisions = newDecision::this.CurrentDecisions
            }
        newScope
    member this.popScope : WriteOnceTypeFieldManager * (Map<SimpleGlobalFieldWithContext,SimpleGlobalField>) =
        let newScope =
            { this with
                SimpleFieldToCurrentArtificialFieldMapping = this.SimpleFieldToCurrentArtificialFieldMapping.Tail;
                SimpleFieldToNewArtificialFieldMapping = this.SimpleFieldToNewArtificialFieldMapping.Tail;
                CurrentDecisions = this.CurrentDecisions.Tail
            }
        (newScope,this.SimpleFieldToNewArtificialFieldMapping.Head)
    member this.getNewArtificialFieldMapping =
        this.SimpleFieldToNewArtificialFieldMapping.Head
    member this.transformExpressionWithCurrentRedirections (expression:SimpleExpression) : WriteOnceExpression =
        //TODO: Take current redirections of fields in fieldManager into account
        expression
    member this.createNewArtificialFieldForField ( field: SimpleGlobalField) : (SimpleGlobalField*WriteOnceTypeFieldManager) =
        // TODO: implement
        //TODO: Variable rewrite here, insert tainted variable
        (field,this)
        
type SimpleStatementsToWriteOnceStatements =

    // TODO: Describe how it works:
    //  ASSIGN:
    //  BRANCH:
    //  MERGE BRANCHES:
    //  LINEARIZE:
    //  The fieldManager keeps the information of the current redirections and allows to introduce new unique artificial variables
    // returns the converted Statements and a list of variables, which got touched in the conversion progress
    member this.simpleStatementToWriteOnceStatementsCached (takenDecisions:SimpleExpression list) (fieldManager:WriteOnceTypeFieldManager) (stmnts:SimpleStatement list) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
        let statementsToMergeTaintedVariables (fieldManager:WriteOnceTypeFieldManager) (fieldManagersWithDecisionAfterSplitToMerge:WriteOnceTypeFieldManager list) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
            //Code, which allows merging of the tainted Variables on a return
            let addEntryToMap (map:Map<SimpleGlobalFieldWithContext,SimpleGlobalField list>) ((actualField,artificialField): SimpleGlobalFieldWithContext*SimpleGlobalField) : Map<SimpleGlobalFieldWithContext,SimpleGlobalField list> =
                if map.ContainsKey actualField then
                    map.Add(actualField,[artificialField])
                else
                    let mapWithoutKey = map.Remove(actualField)
                    mapWithoutKey.Add(actualField, artificialField::(map.Item actualField))
            let fieldAndArtificialFieldPair = fieldManagersToMerge |> List.collect (fun fieldManager -> fieldManager.getNewArtificialFieldMapping |> Map.toList )
            let fieldToArtificialFields = fieldAndArtificialFieldPair |> List.fold addEntryToMap Map.empty
            let transformFieldToArtificialFields ((alreadyTransformed,fieldManager):(WriteOnceStatement list*WriteOnceTypeFieldManager)) (field:SimpleGlobalFieldWithContext) (fieldsInBraches:SimpleGlobalField list) =
                let (transformedTarget,newFieldManager) = fieldManager.createNewArtificialFieldForField field
                // todo: we need to get the decisions taken in every branch of fieldsInBraches and must create for it a specific effect
                let transformFieldInBranch (fieldInBranch:SimpleGlobalField) =                    
                    {
                        WriteOncePossibleEffect.TakenDecisions = "";
                        WriteOncePossibleEffect.TargetEffect = transformedExpression;
                    }
                let effects = fieldsInBraches |> List.map transformFieldInBranch
                let statement = WriteOnceStatement.WriteOnceStatementEvaluateDecisionsParallel( transformedTarget, effects)

                (alreadyTransformed@[statement],newFieldManager)
            fieldToArtificialFields |> Map.fold transformFieldToArtificialFields ([],fieldManager)
            
        let transformSimpleStatement (fieldManager:WriteOnceTypeFieldManager) (statement:SimpleStatement) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
            match statement with
                | SimpleStatement.GuardedCommandStatement (optionsOfGuardedCommand:(( SimpleExpression * (SimpleStatement list) ) list)) -> //Context * Guard * Statements  
                    let transformOption ((guard,sequence) : (SimpleExpression * (SimpleStatement list) )) : ((WriteOnceStatement list )*WriteOnceTypeFieldManager)=
                        let transformedGuard = fieldManager.transformExpressionWithCurrentRedirections guard
                        let takenDecisions = transformedGuard::takenDecisions
                        let (transformedOption,newFieldManager) = this.simpleStatementToWriteOnceStatementsCached takenDecisions fieldManager sequence
                        //TODO: Put takenDecisions in newFieldManager
                        (transformedOption,newFieldManager)                        
                    // BRANCH
                    // Sequential Code of every Branch (flat, without any recursions)
                    let (codeOfBranches,fieldManagersWithDecisionAfterSplit) = optionsOfGuardedCommand |> List.map  transformOption
                                                                                                       |> List.unzip
                    let (codeOfBranchesAggregated) = codeOfBranches |> List.concat
                    // MERGE BRANCHES
                    let (codeToMergeBranches,fieldManagerAfterMerge) = statementsToMergeTaintedVariables fieldManager fieldManagersWithDecisionAfterSplit                    
                    // concat Code of every BRANCH and Code to MERGE
                    (codeOfBranchesAggregated @ codeToMergeBranches,fieldManagerAfterMerge)

                | SimpleStatement.AssignmentStatement (target:SimpleGlobalField, expression:SimpleExpression) -> //Context is only the Context of the Expression. SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)
                    // ASSIGN, Introduce a new artificial field, and update the fieldManager to include the new field
                    let transformedExpression = fieldManager.transformExpressionWithCurrentRedirections expression
                    let (transformedTarget,newFieldManager) = fieldManager.createNewArtificialFieldForField target
                    let effect = {
                            WriteOncePossibleEffect.TakenDecisions = takenDecisions;
                            WriteOncePossibleEffect.TargetEffect = transformedExpression;
                    }
                    let statement = WriteOnceStatement.WriteOnceStatementEvaluateDecisionsParallel( transformedTarget, [effect])
                    ([statement],newFieldManager)
        // LINEARIZE
        // Here we have to transform a LIST of Statements. The fieldManager of the next Statement is the resutling fieldManager of the
        // current statement. Thus we use a fold
        let (transformedStatements,fieldManagerAfterSequence) =
            stmnts |> List.fold (fun (alreadyTransformedStatements,currentFieldManager) statementToTransform ->
                                        let (newStatements,newFieldManager) = transformSimpleStatement currentFieldManager statementToTransform
                                        (alreadyTransformedStatements@newStatements,newFieldManager)
                                ) ([],fieldManager)

        (transformedStatements,fieldManagerAfterSequence)
    
    member this.simpleStatementToWriteOnceStatements (stmnts:SimpleStatement list) : WriteOnceStatement list =
        
        let varFactory = WriteOnceTypeFieldManager.Initialize fields
        // TODO: write a next() for every SimpleField in the SimpleFieldToCurrentArtificialFieldMapping.
        // The effect is the current valuation of the artificial field in the map
        []