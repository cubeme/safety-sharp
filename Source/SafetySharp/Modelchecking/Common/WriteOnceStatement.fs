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
type WriteOnceStatement = {
    Target : WriteOnceGlobalField;
    PossibleEffects : WriteOncePossibleEffect list;
} 


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


type WriteOnceTypeFieldManager = {
    SimpleFieldToInitialFieldMapping : Map<SimpleGlobalFieldWithContext,SimpleGlobalField list>; //map to the initial SimpleGlobalField
    SimpleFieldToCounterMapping : Map<SimpleGlobalFieldWithContext,int> ref; //every time a new artificial field is created, counter is increased. It is "ref" so its value is shared across different instances leading back to the same .Initialize
    SimpleFieldToCurrentArtificialFieldMapping : Map<SimpleGlobalFieldWithContext,SimpleGlobalField list>; //if an artificial field for a reference field is created, put the new field on the stack of artificial fields of this reference field

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
    member this.transformExpressionWithCurrentRedirections (expression:SimpleExpression) : WriteOnceExpression =
        //TODO: Take current redirections of fields in fieldManager into account
        expression
    member this.createNewArtificialFieldForField (field:SimpleGlobalField) : SimpleGlobalField =
        // TODO: implement
        field
        
type SimpleStatementsToWriteOnceStatements =

    // returns the converted Statements and a list of variables, which got touched in the conversion progress
    member this.simpleStatementToWriteOnceStatementsCached (takenDecisions:SimpleExpression list) (fieldManager:WriteOnceTypeFieldManager) (stmnts:SimpleStatement list) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
        let statementsToMergeTaintedVariables (fieldManagers:WriteOnceTypeFieldManager list) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
            //TODO: Write code, which allows merging of the tainted Variables on a return
            ([],newFieldManager)
        let transformSimpleStatement (fieldManager:WriteOnceTypeFieldManager) (statement:SimpleStatement) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
            match statement with
                | SimpleStatement.GuardedCommandStatement (optionsOfGuardedCommand:(( SimpleExpression * (SimpleStatement list) ) list)) -> //Context * Guard * Statements  
                    let transformOption ((guard,sequence) : (SimpleExpression * (SimpleStatement list) )) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
                        let takenDecisions = guard::takenDecisions
                        let (transformedOption,newFieldManager) = this.simpleStatementToWriteOnceStatementsCached takenDecisions fieldManager sequence
                        (transformedOption,newFieldManager)                        
                    // BRANCH
                    // Sequential Code of every Branch (flat, without any recursions)
                    let (codeOfBranches,fieldManagersAfterSplit) = optionsOfGuardedCommand |> List.map  transformOption
                                                                                           |> List.unzip
                    let (codeOfBranchesAggregated) = codeOfBranches |> List.concat
                    // MERGE BRANCHES
                    let (codeToMergeBranches,fieldManagerAfterMerge) = statementsToMergeTaintedVariables fieldManagersAfterSplit
                    // concat Code of every BRANCH and Code to MERGE
                    (codeOfBranchesAggregated @ codeToMergeBranches,fieldManagerAfterMerge)

                | SimpleStatement.AssignmentStatement (target:SimpleGlobalField, expression:SimpleExpression) -> //Context is only the Context of the Expression. SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)
                    // ASSIGN, Introduce artificial field and update fieldManager
                    let transformedExpression = fieldManager.transformExpressionWithCurrentRedirections expression
                    let (transformedTarget,newFieldManager) = (target,fieldManager) //TODO: Variable rewrite here, insert tainted variable
                    let effect = {
                            WriteOncePossibleEffect.TakenDecisions = takenDecisions;
                            WriteOncePossibleEffect.TargetEffect = transformedExpression;
                    }
                    let statement = {
                            WriteOnceStatement.PossibleEffects = [effect];
                            WriteOnceStatement.Target = transformedTarget;
                    }
                    ([statement],newFieldManager)
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

        []