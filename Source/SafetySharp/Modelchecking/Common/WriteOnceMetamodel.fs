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

namespace SafetySharp.Modelchecking


open SafetySharp.Modelchecking


//TODO: Somehow enable the use of DEFINE?!?

// used to annotate, if a value referenced
type internal WriteOnceTimeOfAccess =
    | UseResultOfLastStep // for input fields
    | UseResultOfThisStep // for artificial fields

// There exists a difference between SimpleExpression and WriteOnceExpression:
// Here we need a different FieldAccessor: Depending on if we Want to access the value of the current time step or the value of the last
type internal WriteOnceExpression = 
    /// Represents a constant value which may be e.g. a BooleanLiteral with the values true and false.
    | ConstLiteral of Value : SimpleConstLiteral
    
    /// Represents the application of an unary operator to an expression.
    | UnaryExpression of Operand : WriteOnceExpression * Operator : MMUnaryOperator

    /// Represents the application of a binary operator to two subexpressions.
    | BinaryExpression of LeftExpression : WriteOnceExpression * Operator : MMBinaryOperator * RightExpression : WriteOnceExpression

    /// Represents a field access for reading.
    | FieldAccessExpression of TimeOfAccess: WriteOnceTimeOfAccess * Field : SimpleGlobalField
    

type WriteOnceGlobalField = SimpleGlobalField


type internal WriteOncePossibleEffect = {
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
// Be cautious: If no option matches, the assignment doesn't change anything. (Thus the next value of target is the current value of target).

type internal WriteOnceStatement = 
    | WriteOnceStatementEvaluateDecisionsParallel of Target : (WriteOnceGlobalField) * PossibleEffects : (WriteOncePossibleEffect list) * ElseEffect : (WriteOnceExpression)
    | WriteOnceStatementEvaluateDecisionsSequential of Target : (WriteOnceGlobalField) * PossibleEffects : (WriteOncePossibleEffect list)
    | WriteOnceStatementSimpleAssign of Target : (WriteOnceGlobalField) * Expression : (WriteOnceExpression)
    | WriteOnceStatementSimpleAssignWithCondition of Target : (WriteOnceGlobalField) * Effect : (WriteOncePossibleEffect)
 with
    member this.getTarget =
        match this with
            | WriteOnceStatementEvaluateDecisionsParallel(target,_,_) -> target
            | WriteOnceStatementEvaluateDecisionsSequential(target,_) -> target
            | WriteOnceStatementSimpleAssign(target,_) -> target
            | WriteOnceStatementSimpleAssignWithCondition(target,_) -> target
            

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
// TODO: include in name something like "Branch" or Decisions BranchAndFieldManager? Or TransformationManager
type internal WriteOnceTypeFieldManager = {
    // static across a model. TODO: Maybe we can remove it
    SimpleFieldToInitialFieldMapping : Map<SimpleGlobalFieldWithContext,SimpleGlobalField>; //map to the initial SimpleGlobalField
    // static across a scope. Changes with scopes. Organised as stacks. The head elements are the current elements. on a popScope the head elements are just thrown away
    SimpleFieldToCurrentRedirectionFieldMapping : (Map<SimpleGlobalFieldWithContext,WriteOnceTimeOfAccess*SimpleGlobalField>) list; //if an artificial field for a reference field is created, link the artificial fields to the field it overwrites
    SimpleFieldToNewArtificialFieldMapping : (Map<SimpleGlobalFieldWithContext,WriteOnceTimeOfAccess*SimpleGlobalField>) list; //same as above, but only the fields introduced in this of the current scope. If a field is not "overwritten" in this scope, the map does not contain it.
    CurrentDecisions : (WriteOnceExpression list); //A Stack will all Decisions taken to this Branch
    // Following items are shared across all managers with the same .Initialize. They should only be changed internally.
    SimpleFieldToArtificialCounterShared : Map<SimpleGlobalFieldWithContext,int> ref; //every time a new artificial field is created, counter is increased. It is "ref" so its value is shared across different instances leading back to the same .Initialize
    CreatedArtificialFieldsShared : (SimpleGlobalField list) ref; //every time a new artificial field is created by the manager, it is associated with this manager. It is "ref" so its value is shared across different instances leading back to the same .Initialize

} with
    static member Initialize (fields:SimpleGlobalField list) =
        let initialSimpleFieldToInitialFieldMapping: Map<SimpleGlobalFieldWithContext,SimpleGlobalField>=
            let createEntry (field:SimpleGlobalField) : (SimpleGlobalFieldWithContext*SimpleGlobalField) =
                (field.getSimpleGlobalFieldWithContext,field)
            fields |> List.map createEntry
                   |> Map.ofList
        let initialSimpleFieldToInitialRedirectionFieldMapping: Map<SimpleGlobalFieldWithContext,WriteOnceTimeOfAccess*SimpleGlobalField>=
            let createEntry (field:SimpleGlobalField) : (SimpleGlobalFieldWithContext*(WriteOnceTimeOfAccess*SimpleGlobalField)) =
                (field.getSimpleGlobalFieldWithContext,(WriteOnceTimeOfAccess.UseResultOfLastStep,field))
            fields |> List.map createEntry
                   |> Map.ofList
        let initialSimpleFieldToArtificialCounterShared: Map<SimpleGlobalFieldWithContext,int>=
            let createEntry (field:SimpleGlobalField) : (SimpleGlobalFieldWithContext*int) =
                (field.getSimpleGlobalFieldWithContext,0)
            fields |> List.map createEntry
                   |> Map.ofList
        {
            WriteOnceTypeFieldManager.SimpleFieldToInitialFieldMapping = initialSimpleFieldToInitialFieldMapping;
            WriteOnceTypeFieldManager.SimpleFieldToCurrentRedirectionFieldMapping = [initialSimpleFieldToInitialRedirectionFieldMapping];
            WriteOnceTypeFieldManager.SimpleFieldToNewArtificialFieldMapping = [Map.empty<SimpleGlobalFieldWithContext,WriteOnceTimeOfAccess*SimpleGlobalField>];
            WriteOnceTypeFieldManager.CurrentDecisions = [];
            WriteOnceTypeFieldManager.SimpleFieldToArtificialCounterShared=ref initialSimpleFieldToArtificialCounterShared;
            WriteOnceTypeFieldManager.CreatedArtificialFieldsShared= ref [];
        }
    member this.pushScope (newDecision:WriteOnceExpression) : WriteOnceTypeFieldManager =
        let emptyNewMapping = Map.empty<SimpleGlobalFieldWithContext,WriteOnceTimeOfAccess*SimpleGlobalField>
        let currentlyKnownMapping = this.SimpleFieldToCurrentRedirectionFieldMapping.Head
        let newScope = 
            { this with
                SimpleFieldToCurrentRedirectionFieldMapping = currentlyKnownMapping::this.SimpleFieldToCurrentRedirectionFieldMapping;
                SimpleFieldToNewArtificialFieldMapping = emptyNewMapping::this.SimpleFieldToNewArtificialFieldMapping;
                CurrentDecisions = newDecision::this.CurrentDecisions
            }
        newScope
    member this.popScope : WriteOnceTypeFieldManager * (Map<SimpleGlobalFieldWithContext,WriteOnceTimeOfAccess*SimpleGlobalField>) =
        let newScope =
            { this with
                SimpleFieldToCurrentRedirectionFieldMapping = this.SimpleFieldToCurrentRedirectionFieldMapping.Tail;
                SimpleFieldToNewArtificialFieldMapping = this.SimpleFieldToNewArtificialFieldMapping.Tail;
                CurrentDecisions = this.CurrentDecisions.Tail;
            }
        (newScope,this.SimpleFieldToNewArtificialFieldMapping.Head)
    member this.getTakenDecisions =
        this.CurrentDecisions
    member this.getNewArtificialFieldMapping =
        this.SimpleFieldToNewArtificialFieldMapping.Head
    member this.getCurrentRedirection (field:SimpleGlobalFieldWithContext) : (WriteOnceTimeOfAccess*SimpleGlobalField) =
        this.SimpleFieldToCurrentRedirectionFieldMapping.Head.Item field

    member this.transformExpressionWithCurrentRedirections (expression:SimpleExpression) : WriteOnceExpression =
        match expression with
            | SimpleExpression.ConstLiteral (literal:SimpleConstLiteral) ->
                WriteOnceExpression.ConstLiteral(literal)
            | SimpleExpression.UnaryExpression (operand:SimpleExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformExpressionWithCurrentRedirections operand
                WriteOnceExpression.UnaryExpression(transformedOperand,operator)
            | SimpleExpression.BinaryExpression (leftExpression:SimpleExpression, operator:MMBinaryOperator, rightExpression : SimpleExpression) ->
                let transformedLeft = this.transformExpressionWithCurrentRedirections leftExpression
                let transformedRight = this.transformExpressionWithCurrentRedirections rightExpression
                WriteOnceExpression.BinaryExpression(transformedLeft,operator,transformedRight)
            | SimpleExpression.FieldAccessExpression (field:SimpleGlobalField) ->
                //Take current redirections of fields in fieldManager into account
                let fieldRef = this.getCurrentRedirection field.getSimpleGlobalFieldWithContext
                WriteOnceExpression.FieldAccessExpression(fieldRef)
                
    member this.createNewArtificialFieldForField ( field: SimpleGlobalFieldWithContext) : (SimpleGlobalField*WriteOnceTypeFieldManager) =
        // get counter for the new variable and increase the counter
        let currentNumber = (this.SimpleFieldToArtificialCounterShared.Value.Item field)+1
        this.SimpleFieldToArtificialCounterShared.Value <-
            (this.SimpleFieldToArtificialCounterShared.Value.Add(field,currentNumber))
        let newFieldWithContext= field.createDerivedFieldWithStandardValues currentNumber
        let newArtificialField = SimpleGlobalField.FieldWithContext(newFieldWithContext)
        this.CreatedArtificialFieldsShared.Value <-
            (newArtificialField::this.CreatedArtificialFieldsShared.Value)
            
        let newSimpleFieldToCurrentRedirectionFieldMapping = 
            this.SimpleFieldToCurrentRedirectionFieldMapping.Head.Add(field,(WriteOnceTimeOfAccess.UseResultOfThisStep,newArtificialField))
        let newSimpleFieldToNewArtificialFieldMapping = 
            this.SimpleFieldToNewArtificialFieldMapping.Head.Add(field,(WriteOnceTimeOfAccess.UseResultOfThisStep,newArtificialField))

        let newFieldManager =
            { this with
                SimpleFieldToCurrentRedirectionFieldMapping = newSimpleFieldToCurrentRedirectionFieldMapping::this.SimpleFieldToCurrentRedirectionFieldMapping.Tail;
                SimpleFieldToNewArtificialFieldMapping = newSimpleFieldToNewArtificialFieldMapping::this.SimpleFieldToNewArtificialFieldMapping.Tail;
            }
        (newArtificialField,newFieldManager)
        
//initialFields contains all fields of every partition
type internal SimpleStatementsToWriteOnceStatements(initialFields:SimpleGlobalField list) =
    
    let initialFieldManager = WriteOnceTypeFieldManager.Initialize initialFields

    // TODO: Describe how it works:
    //  ASSIGN:
    //  BRANCH:
    //  MERGE BRANCHES:
    //  LINEARIZE:
    //  NEXTSTEP:
    //  The fieldManager keeps the information of the current redirections and allows to introduce new unique artificial variables
    // returns the converted Statements and a list of variables, which got touched in the conversion progress
    member this.simpleStatementToWriteOnceStatementsCached (fieldManager:WriteOnceTypeFieldManager) (stmnts:SimpleStatement list) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
        
        let statementsToMergeTaintedVariables (fieldManager:WriteOnceTypeFieldManager) (fieldManagersAfterSplitToMerge:WriteOnceTypeFieldManager list) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
            //Code, which allows merging of the tainted Variables on a return
            let addEntryToMap (map:Map<SimpleGlobalFieldWithContext,(WriteOnceTimeOfAccess*SimpleGlobalField) list>)
                              ((actualField,artificialField): SimpleGlobalFieldWithContext*(WriteOnceTimeOfAccess*SimpleGlobalField)) 
                                        : Map<SimpleGlobalFieldWithContext,(WriteOnceTimeOfAccess*SimpleGlobalField) list> =
                if not (map.ContainsKey actualField) then
                    map.Add(actualField,[artificialField])
                else
                    map.Add(actualField, artificialField::(map.Item actualField))
            let pairsOfReferenceToArtificialField = fieldManagersAfterSplitToMerge |> List.collect (fun fieldManager -> fieldManager.getNewArtificialFieldMapping |> Map.toList )
            let referencesToArtificialFields = pairsOfReferenceToArtificialField |> List.fold addEntryToMap Map.empty
            let assignToFieldTheValuesOfItsArtificialFields ((alreadyTransformed,fieldManager):(WriteOnceStatement list*WriteOnceTypeFieldManager)) 
                                                            (field:SimpleGlobalFieldWithContext)
                                                            (fieldsInBraches:(WriteOnceTimeOfAccess*SimpleGlobalField) list) 
                                                                : (WriteOnceStatement list * WriteOnceTypeFieldManager)=
                //ELSE: If none of the branch matches, assign to the transformedTarget the value in the redirected field (not the origin field)
                let currentRedirectionOfField = fieldManager.getCurrentRedirection field
                let elseEffect = WriteOnceExpression.FieldAccessExpression currentRedirectionOfField
                // create artificial Field
                let (transformedTarget,newFieldManager) = fieldManager.createNewArtificialFieldForField field
                // we get the decisions taken in every branch of fieldsInBraches and create for it a specific effect
                let transformFieldInBranch ((timeofAccess,fieldInBranch):WriteOnceTimeOfAccess*SimpleGlobalField) =
                    let transformedExpression = WriteOnceExpression.FieldAccessExpression(timeofAccess,fieldInBranch)
                    {
                        WriteOncePossibleEffect.TakenDecisions = newFieldManager.getTakenDecisions;
                        WriteOncePossibleEffect.TargetEffect = transformedExpression;
                    }                
                let effects = fieldsInBraches |> List.map transformFieldInBranch
                                
                let statement = WriteOnceStatement.WriteOnceStatementEvaluateDecisionsParallel( transformedTarget, effects, elseEffect)

                (alreadyTransformed@[statement],newFieldManager)
            referencesToArtificialFields |> Map.fold assignToFieldTheValuesOfItsArtificialFields ([],fieldManager)
            
        let transformSimpleStatement (fieldManager:WriteOnceTypeFieldManager) (statement:SimpleStatement) : (WriteOnceStatement list*WriteOnceTypeFieldManager) =
            match statement with
                | SimpleStatement.GuardedCommandStatement (optionsOfGuardedCommand:(( SimpleExpression * (SimpleStatement list) ) list)) -> //Context * Guard * Statements  
                    let transformOption ((guard,sequence) : (SimpleExpression * (SimpleStatement list) )) : ((WriteOnceStatement list )*WriteOnceTypeFieldManager)=
                        let transformedGuard = fieldManager.transformExpressionWithCurrentRedirections guard
                        let newScopeFieldManager = fieldManager.pushScope transformedGuard
                        let (transformedOption,newFieldManager) = this.simpleStatementToWriteOnceStatementsCached newScopeFieldManager sequence
                        //TODO: Put takenDecisions in newFieldManager
                        (transformedOption,newFieldManager)                        
                    // BRANCH
                    // Sequential Code of every Branch (flat, without any recursions)
                    let (codeOfBranches,fieldManagersAfterSplitToMerge) = optionsOfGuardedCommand |> List.map  transformOption
                                                                                                  |> List.unzip
                    let (codeOfBranchesAggregated) = codeOfBranches |> List.concat
                    // MERGE BRANCHES
                    let (codeToMergeBranches,fieldManagerAfterMerge) = statementsToMergeTaintedVariables fieldManager fieldManagersAfterSplitToMerge                    
                    // concat Code of every BRANCH and Code to MERGE
                    (codeOfBranchesAggregated @ codeToMergeBranches,fieldManagerAfterMerge)

                | SimpleStatement.AssignmentStatement (target:SimpleGlobalField, expression:SimpleExpression) -> //Context is only the Context of the Expression. SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)
                    // ASSIGN, Introduce a new artificial field, and update the fieldManager to include the new field
                    let transformedExpression = fieldManager.transformExpressionWithCurrentRedirections expression
                    let (transformedTarget,newFieldManager) = fieldManager.createNewArtificialFieldForField target.getSimpleGlobalFieldWithContext
                    // The TakenDecisions are processed in the MERGE-Stage
                    (*let effect = {
                            WriteOncePossibleEffect.TakenDecisions = newFieldManager.getTakenDecisions;
                            WriteOncePossibleEffect.TargetEffect = transformedExpression;
                    }*)
                    let statement = WriteOnceStatement.WriteOnceStatementSimpleAssign( transformedTarget, transformedExpression)
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
    

    //fieldsOfPartition only contains the fields of the current partition
    //RELY: smnts contains every update and binding-stmnt of a partition. Every writing access to a field access of this partition is included in stmnts.
    //      Reason: Artificial fields are introduced and their name relies on the name of a kfield they are based on. Thus fields are not duplicated.
    member this.simpleStatementToWriteOnceStatements (fieldsOfPartition:SimpleGlobalField list) (stmnts:SimpleStatement list) : WriteOnceStatement list =
        
        let fieldManager = initialFieldManager
        let (transformedStatements,fieldManagerAfterSequence) = this.simpleStatementToWriteOnceStatementsCached fieldManager stmnts
        //  NEXTSTEP:
        // write an assignment for every SimpleGlobalField (get the current redirection from the fieldManagerAfterSequence)
        let assignmentsToCurrentValuationStatements = 
            let transformField (field:SimpleGlobalField) : WriteOnceStatement =
                let (timeOfAccess,redirectedToField) = fieldManagerAfterSequence.getCurrentRedirection field.getSimpleGlobalFieldWithContext
                let redirectedToFieldExpression = WriteOnceExpression.FieldAccessExpression(timeOfAccess,redirectedToField)
                // No decisions made, because we didn't branch here
                let statement = WriteOnceStatement.WriteOnceStatementSimpleAssign( field, redirectedToFieldExpression)
                statement
            fieldsOfPartition |> List.map transformField
            
        // The effect is the current valuation of the artificial field in the map
        transformedStatements @ assignmentsToCurrentValuationStatements


    member this.getAllArtificialFields() : SimpleGlobalField list = 
        initialFieldManager.CreatedArtificialFieldsShared.Value
    
    member this.getAllFields() : SimpleGlobalField list = 
        initialFields @ this.getAllArtificialFields()