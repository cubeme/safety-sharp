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

//  * The Simplified Metamodel is a flat version of the Full Metamodel without the concept of Components and Structure.
//    It is somehow removing the object orientation from the Full Metamodel.
//    The conversion is done by creating for each field of every instance of a componenta a global field
//    ("Instance of a Component" * "Field of Component" -> "Global Field").
//    Expressions and Statements in the Simplified Metamodel know the Global Field they apply to.
//    The conversation is done by shifting the concrete Component Instance of an Expression into the Expressions.
//    ("Instance of Component" * "Expression in Full Metamodel" -> "Expression in Simplified Metamodel)
//    This is easily possible, because dynamic instantitation of Components is not possible in our semantics.
//  * A Simplified Metamodel consists of a Sequence of SimpleStatements which are executed each (Macro-)Step. consisting of
//      - One Sequence of SimpleStatements per Partition for its Updates
//      - One Sequence of SimpleStatements per Binding
//  * A SimpleExpressions is an Expression, which knows its context (the component it is used in)
//  * A SimpleStatement is either an Assignments or a Guarded Command
//      - an Assignments = SimpleGlobalField * SimpleExpression
//      - a Guarded Command = List of Options, Option = Guards (Expression) and a Sequence (List of SimpleStatements)
//  * A SimpleGlobalField is a struct, which encapsulates all information about a Global Field in the Simplified Metamodel

type MMModelObject = SafetySharp.Metamodel.ModelObject
type MMPartitionObject = SafetySharp.Metamodel.PartitionObject
type MMComponentObject = SafetySharp.Metamodel.ComponentObject
type MMFieldObject = SafetySharp.Metamodel.FieldObject
type MMConfiguration = SafetySharp.Metamodel.Configuration // <--------- main artifact

type MMTypeSymbol = SafetySharp.Metamodel.TypeSymbol
type MMFieldSymbol = SafetySharp.Metamodel.FieldSymbol
type MMParameterSymbol = SafetySharp.Metamodel.ParameterSymbol
type MMMethodSymbol = SafetySharp.Metamodel.MethodSymbol
type MMComponentReferenceSymbol = SafetySharp.Metamodel.ComponentReferenceSymbol
type MMComponentSymbol = SafetySharp.Metamodel.ComponentSymbol
type MMPartitionSymbol = SafetySharp.Metamodel.PartitionSymbol
type MMModelSymbol = SafetySharp.Metamodel.ModelSymbol

type MMExpression = SafetySharp.Metamodel.Expression
type MMUnaryOperator = SafetySharp.Metamodel.UnaryOperator
type MMBinaryOperator = SafetySharp.Metamodel.BinaryOperator
type MMStatement = SafetySharp.Metamodel.Statement
type MMFormula = SafetySharp.Metamodel.Formula
type MMUnaryFormulaOperator = SafetySharp.Metamodel.UnaryFormulaOperator
type MMBinaryFormulaOperator = SafetySharp.Metamodel.BinaryFormulaOperator
type MMMethodBodyResolver = Map<MMComponentSymbol * MMMethodSymbol, MMStatement>


// TODO: Ensure reverse mapping is working for debugging purposes
//       Traceability: Introduce a element, which allows it to connect SimpleExpressions with MMExpressions. Three ways to achieve this
//       - Duplicate every discriminated union case of SimpleStatement, SimpleExpression, SimpleGlobalField to allow the case
//         that the field is artificial or references a MM-equivalent
//              (contra: bloats types)
//       - Introduce a mapping
//              (contra: bloats recursive call parameters and return parameters)
//       - Introduce in every discriminated union case an optional element
//              (contra: drag along information not really necessary in many cases)
//       - Introduce one extra case: "MMReference of MMX * SimpleX" and member-Functions "dereference" and "recursiveDereference"
//              (I think I'll take this approach)

// Maybe TODO:
// The Simplified Metamodel is still connected to the Full Metamodel, because it links to some of its artifacts
// (Context uses MMComponentObject,SimpleExpression knows MMComponentObject...). If we get rid of it and replace it with a simple mapping, the Simplified
// Metamodel is completly independent of the Full Metamodel, testing is easier. Until now we don't really need it. This keeps the code smaller and less redundancy.

// TODO: Move much of the stuff into file SimplifiedMetamodel

type ReverseComponentObjectMap = Map<string,MMComponentReferenceSymbol>

type Context = {
    hierarchicalAccess : string list; // hierarchicalAccess does not contain the name of the root Component. Last object is the name of the root-Component; head is a subComponent of its parent:  subComponent1::(parentOfSubComponent1)*. Construction is done in type SimpleGlobalFieldCache
    rootComponentName : string; //only the name of the root component
}

type SimpleConstLiteral = 
    /// Represents a Boolean literal, that is, either <c>true</c> or <c>false</c>.
    | BooleanLiteral of Value : bool

    /// Represents an integer value.
    | IntegerLiteral of Value : int

    /// Represents a decimal value.
    | DecimalLiteral of Value : decimal
    with
        static member convertFromObject (value:obj) =
            match value with
                | :? int as value     -> value |> SimpleConstLiteral.IntegerLiteral
                | :? bool as value    -> value |> SimpleConstLiteral.BooleanLiteral
                | :? decimal as value -> value |> SimpleConstLiteral.DecimalLiteral
                | :? float as value   -> value |> decimal
                                               |> SimpleConstLiteral.DecimalLiteral
                | :? float32 as value -> value |> decimal
                                               |> SimpleConstLiteral.DecimalLiteral
                | _ -> failwith "NotImplementedYet"
        static member convertFromObjectList (values:obj list) =
            values |> List.map SimpleConstLiteral.convertFromObject

[<StructuralEquality;StructuralComparison>]
type SimpleGlobalFieldWithContext = {
    Context : Context;
    FieldSymbol: MMFieldSymbol;
    InitialValues : SimpleConstLiteral list;
}

type SimpleGlobalField =
    | FieldLinkedToMetamodel of ComponentObject : MMComponentObject * Field : SimpleGlobalFieldWithContext
    //| FieldArtificialWithReferenceToFieldInMetamodel of ReferencedField : SimpleGlobalField * FieldName : string //ReferencedField
 // | FieldArtifical of Context : (Context option) * FieldSymbol : MMFieldSymbol * InitialValues : (obj list)
    with
        member this.getFieldSymbol =
            match this with
                | SimpleGlobalField.FieldLinkedToMetamodel (_,field)-> field.FieldSymbol
        member this.getInitialValues =
            match this with
                | SimpleGlobalField.FieldLinkedToMetamodel (_,field)-> field.InitialValues
        member this.hasContext =
            match this with
                | SimpleGlobalField.FieldLinkedToMetamodel _ -> true
                | _ -> false
        member this.getContext =
            match this with
                | SimpleGlobalField.FieldLinkedToMetamodel (_,field) -> field.Context
                | _ -> failwith "this SimpleGlobalField has no context"
        member this.getSimpleGlobalFieldWithContext =
            match this with
                | SimpleGlobalField.FieldLinkedToMetamodel (_,field) -> field
                | _ -> failwith "this is not a SimpleGlobalField which contains a field of the type SimpleGlobalFieldWithContext"


// A SimpleExpression knows the Context of its variables (We use MMExpression, because it already offers this functionality for Formulas)
type SimpleExpression = 
    /// Represents a constant value which may be e.g. a BooleanLiteral with the values true and false.
    | ConstLiteral of Value : SimpleConstLiteral
    
    /// Represents the application of an unary operator to an expression.
    | UnaryExpression of Operand : SimpleExpression * Operator : MMUnaryOperator

    /// Represents the application of a binary operator to two subexpressions.
    | BinaryExpression of LeftExpression : SimpleExpression * Operator : MMBinaryOperator * RightExpression : SimpleExpression

    /// Represents a field access, either for reading or writing. The component refrence is guaranteed to be 'None' within
    /// method bodies and guaranteed to be some valid reference in formulas.
    | FieldAccessExpression of Field : SimpleGlobalField



// A simpleStatement has only assignments and guarded commands. Also Assignments are defined on SimpleGlobalFields
type SimpleStatement = 
    | GuardedCommandStatement of (SimpleExpression * (SimpleStatement list) ) list //Guard (which knows its Context) * Statements
    | AssignmentStatement of Target : SimpleGlobalField * Expression : SimpleExpression //Expression (knows its Context). SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)





// Only use in this file
type ResolverForSimpleGlobalFields = Map<string*string,SimpleGlobalField>

    
type ContextCache (configuration:MMConfiguration) =
        // _once_ calculated and cached information for internal use
        let model = configuration.ModelObject

        let rootComponentToName : Map<string,string> =
            let counter = ref 0
            model.Partitions |> List.map (fun elem -> elem.RootComponent)
                             |> List.map (fun elem -> counter:=!counter+1
                                                      let counterString = (!counter).ToString()
                                                      (elem.Name,"root"+counterString))
                             |> Map.ofList

        // accessor and helper functions (internal use)
        let nameOfRootComponent (rootComponent:MMComponentObject) : string =
            rootComponentToName.Item rootComponent.Name
            
        // accessor and helper functions (external use)
        member this.createContextOfRootComponent (partition:MMPartitionObject) : Context =
            {
                Context.hierarchicalAccess = [];
                Context.rootComponentName = nameOfRootComponent partition.RootComponent;
            }
        member this.createContextForSubcomponent (parentContext:Context) (newElementName:string) (comp:MMComponentObject) : Context =
            {
                Context.hierarchicalAccess = newElementName::parentContext.hierarchicalAccess; //parentsAndMe
                Context.rootComponentName = parentContext.rootComponentName;
            }


        
    // this is extraced from ModelInformationCache, to keep the code together which belongs together
    // TODO: Sort and categorize:
    //      - _once_ calculated and cached information for internal use
    //      - _once_ calculated and cached information for external use (better write accessor functions for it)        
    //      - accessor and helper functions (internal use)
    //      - accessor and helper functions (external use)
type SimpleGlobalFieldCache (contextCache:ContextCache, configuration:MMConfiguration) =
        // this should only calculate and _cache_ information for the transformation to
        // SimpleStatements/SimpleExpressions and not be used from outside this file
        
        let model = configuration.ModelObject
        
        let reverseComponentObjects : ReverseComponentObjectMap =
            // string is the unique name of the ComponentObject 
            // ReverseComponentObjectMap = Map<string,MMComponentReferenceSymbol>      
            model.ComponentObjects |> Map.toList
                                   |> List.map (fun (reference,compobject) -> (compobject.Name,reference))
                                   |> Map.ofList


        let ComponentObjectToComponentReference (comp:MMComponentObject) : MMComponentReferenceSymbol =
            reverseComponentObjects.Item comp.Name

        let getSubComponentObjects (subcomponentMap : Map<MMComponentReferenceSymbol, MMComponentObject>) : ((string*MMComponentObject) list) =
            subcomponentMap |> Map.fold (fun acc key value -> (key.Name,value)::acc) []
    
        let getFieldObjects (fieldMap : Map<MMFieldSymbol, MMFieldObject>) : (MMFieldObject list) =
            fieldMap |> Map.fold (fun acc key value -> value::acc) []

            
        let simpleGlobalFields : SimpleGlobalField list =
            // This function works like this: collectFromPartition -> collectFromComponent -> collectFieldInThisComponent
            // It traverses the model and generates a list of all fields with all necessary information about the field (SimpleGlobalField)
            let rec collectFromComponent (componentObject:MMComponentObject) (myContext:Context) : SimpleGlobalField list =
                let collectedInSubcomponents : SimpleGlobalField list =
                    (getSubComponentObjects componentObject.Subcomponents) |> List.collect (fun (name,comp) -> collectFromComponent comp (contextCache.createContextForSubcomponent myContext name comp) )
                let collectFieldInThisComponent (fieldobject:MMFieldObject) =
                    let field = {
                        SimpleGlobalFieldWithContext.Context=myContext;
                        SimpleGlobalFieldWithContext.FieldSymbol=fieldobject.FieldSymbol;
                        SimpleGlobalFieldWithContext.InitialValues=(SimpleConstLiteral.convertFromObjectList fieldobject.InitialValues);
                    }
                    SimpleGlobalField.FieldLinkedToMetamodel(componentObject,field)
                let collectedInThisComponent = (getFieldObjects componentObject.Fields) |> List.map collectFieldInThisComponent 
                collectedInThisComponent @ collectedInSubcomponents
            let collectFromPartition (partition:MMPartitionObject) : SimpleGlobalField list  =
                let contextOfCurrentPartitionRootComponent = contextCache.createContextOfRootComponent partition
                collectFromComponent partition.RootComponent contextOfCurrentPartitionRootComponent
            model.Partitions |> List.collect collectFromPartition
        
        // this resolves a field access inside a component to a SimpleGlobalField.FieldLinkedToMetamodel
        let fieldAccessInACompomonentToSimpleGlobalFieldMap : ResolverForSimpleGlobalFields = 
            //type ResolverForFormulas = Map<string*string,SimpleGlobalField> first string is the unique componentName, second string is fieldName
            let converter (elem:SimpleGlobalField) =
                match elem with
                    | SimpleGlobalField.FieldLinkedToMetamodel(componentObject:MMComponentObject, field:SimpleGlobalFieldWithContext) ->
                        [((componentObject.Name, field.FieldSymbol.Name),elem)] //return as list to allow List.collect
                    | _ -> []
            simpleGlobalFields |> List.collect converter
                               |> Map.ofList
        
        let resolveFieldAccessInsideAComponent (comp:MMComponentObject) (field:MMFieldSymbol) : SimpleGlobalField =
            let componentObjectName = comp.Name
            let fieldName = field.Name
            fieldAccessInACompomonentToSimpleGlobalFieldMap.Item (componentObjectName,fieldName)

        
        member this.createSimpleFieldAccessExpression (field:MMFieldSymbol) (comp:MMComponentObject): SimpleExpression =
            let componentReference = ComponentObjectToComponentReference comp
            let simpleGlobalField = this.resolveFieldAccessInsideAFormula componentReference field
            SimpleExpression.FieldAccessExpression(simpleGlobalField)

        member this.getSimpleGlobalFields : SimpleGlobalField list =
            simpleGlobalFields
                           
        member this.resolveFieldAccessInsideAFormula (referenceSymbol:MMComponentReferenceSymbol) (field:MMFieldSymbol) : SimpleGlobalField =
            let componentObject = model.ComponentObjects.Item referenceSymbol
            let componentObjectName = componentObject.Name
            let fieldName = field.Name
            fieldAccessInACompomonentToSimpleGlobalFieldMap.Item (componentObjectName,fieldName)
        
    
    
    
// Many steps are a sequence. Only use in this file
type MMStepInfo = {
        context : Context;
        componentObject:MMComponentObject;
        statement : MMStatement;
    }

(*
//conversion should be done for the complete Metamodel

type SimplifiedMetamodel = 
{
    Partitions : (Name*(Fields, Update:(SimpleStatement list)) list);
    Bindings : ((SimpleStatement list) list); //Or interleave Binding with Partitions. Semantic not relly defined, yet.
    Formulas : Formulas : list
} with
    generate (Metamodel:MMConfiguration)
*)

type MetamodelToSimplifiedMetamodel (configuration:MMConfiguration) =
    let contextCache = ContextCache(configuration)
    let fieldCache = SimpleGlobalFieldCache(contextCache,configuration)

    let rec resolveTargetOfAnAssignment (componentObject:MMComponentObject) (context:Context) (expression:MMExpression) : SimpleGlobalField =
        // Use resolveSimpleGlobalFieldInCode only for expression inside components and not in formulas
        // Example of usage: Used on the left side of assignments
        match expression with
            | MMExpression.BooleanLiteral (value:bool) ->
                failwith "target of field access cannot be a constant value"
            | MMExpression.IntegerLiteral (value:int) ->
                failwith "target of field access cannot be a constant value"
            | MMExpression.DecimalLiteral (value:decimal) ->
                failwith "target of field access cannot be a constant value"
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                failwith "NotImplementedYet" //TODO: Is this even useful? Maybe for array access...
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                failwith "NotImplementedYet" //TODO: Is this even useful? Maybe for array access...
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, comp:MMComponentReferenceSymbol option) ->
                if comp.IsSome then
                    // if comp is set, then this expression is an expression inside a formula
                    failwith "Use resolveTargetOfAnAssignment only for expression inside components and not in formulas"
                else
                    // TODO: Better retrieve it from the cache than reconstruct it here
                    let fieldObject = (componentObject.Fields.Item field)
                    let fieldWithContext = {
                        SimpleGlobalFieldWithContext.Context=context;
                        SimpleGlobalFieldWithContext.FieldSymbol=field;
                        SimpleGlobalFieldWithContext.InitialValues=(SimpleConstLiteral.convertFromObjectList fieldObject.InitialValues);
                    }
                    SimpleGlobalField.FieldLinkedToMetamodel(componentObject,fieldWithContext)
    
    let rec transformMMExpressionInsideAComponentToSimpleExpression (fieldCache:SimpleGlobalFieldCache) (comp:MMComponentObject) (expression:MMExpression) : SimpleExpression =
        match expression with
            | MMExpression.BooleanLiteral (value:bool) -> SimpleExpression.ConstLiteral(SimpleConstLiteral.BooleanLiteral(value))
            | MMExpression.IntegerLiteral (value:int) ->  SimpleExpression.ConstLiteral(SimpleConstLiteral.IntegerLiteral(value))
            | MMExpression.DecimalLiteral (value:decimal) -> SimpleExpression.ConstLiteral(SimpleConstLiteral.DecimalLiteral(value))
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                let transformedOperand = transformMMExpressionInsideAComponentToSimpleExpression fieldCache comp operand
                SimpleExpression.UnaryExpression(transformedOperand,operator)
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                let transformedLeft = transformMMExpressionInsideAComponentToSimpleExpression fieldCache comp leftExpression
                let transformedRight = transformMMExpressionInsideAComponentToSimpleExpression fieldCache comp rightExpression
                SimpleExpression.BinaryExpression(transformedLeft,operator,transformedRight)
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    fieldCache.createSimpleFieldAccessExpression field comp
                else
                    //called inside a formula or already transformed
                    failwith "Use transformExpressionInsideAComponent only for expression inside untransformed components and not in formulas"

    let rec transformMMStepInfosToSimpleStatements (fieldCache:SimpleGlobalFieldCache) (methodBodyResolver:MMMethodBodyResolver) (collected:SimpleStatement list) (toTransform:MMStepInfo list) : SimpleStatement list =
        // Properties of the result:
        //   - TODO: Return of Statements are rewritten to Assignments of the caller function
        //   -       Variables may be needed to be introduced (?!?)
        //   -       parameter: (targetOfAssignmentStack:(Expression option) list)
        // pattern in this function: take _first_ item of toTransform
        //                              - either expand it and put the expanded into the _front_ of the list toTransform
        //                              - or process it and append the result to the _end_ of collected
        if toTransform.IsEmpty then
            collected
        else
            let firstItem = toTransform.Head
            let statementToProcess = firstItem.statement
            let componentObject = firstItem.componentObject
            let contextOfStatement = firstItem.context            
            let coverStatementWithContext (statement:MMStatement) =
                {
                    MMStepInfo.context=contextOfStatement;
                    MMStepInfo.statement=statement;
                    MMStepInfo.componentObject=componentObject;
                }
            match statementToProcess with
                | MMStatement.EmptyStatement ->
                    let newToTransform = toTransform.Tail
                    transformMMStepInfosToSimpleStatements fieldCache methodBodyResolver collected newToTransform
                | MMStatement.BlockStatement (statements : MMStatement list) ->
                    let expandedBlockStatement = statements |> List.map coverStatementWithContext
                    let newToTransform = expandedBlockStatement @ toTransform.Tail
                    transformMMStepInfosToSimpleStatements fieldCache methodBodyResolver collected newToTransform
                | MMStatement.ReturnStatement (expression : MMExpression option) ->
                    failwith "NotImplementedYet"
                    //TODO: transformStatement needs additional new optional Argument: the value, to which
                    //      the return gets assigned to. Either a real existing value or a temporary variable
                    //      which should also be assigned to. This temporary variable needs be be declared, too.
                    //      Statement gets rewritten to an MMStatement.AssignmentStatement
                    //      and the rest of the sequence is ignored.
                    //Better solution: There is function, which brings all statements in the correct order.
                    //      (for the partition-update and every partition-binding there is exactly one flatten
                    //      order for the execution of the statements). In this function, every ReturnStatement
                    //      needs to be replaced. Thus this case should never be reached
                | MMStatement.GuardedCommandStatement (guardedStmnts:(MMExpression * MMStatement) list) ->
                    let transformOption ((guard,stmnt):MMExpression * MMStatement) :(SimpleExpression*(SimpleStatement list))=
                        let transformedGuard = transformMMExpressionInsideAComponentToSimpleExpression fieldCache componentObject guard
                        let coveredStmnt = coverStatementWithContext stmnt
                        let transformedStmnts = transformMMStepInfosToSimpleStatements fieldCache methodBodyResolver [] [coveredStmnt]
                        (transformedGuard,transformedStmnts)
                    let newToTransform = toTransform.Tail
                    let transformedGuardedCommand = guardedStmnts |> List.map transformOption
                                                                  |> SimpleStatement.GuardedCommandStatement
                    transformMMStepInfosToSimpleStatements fieldCache methodBodyResolver (collected @ [transformedGuardedCommand]) newToTransform

                | MMStatement.AssignmentStatement (target : MMExpression, expression : MMExpression) ->
                    //resolveTargetOfAnAssignment
                    let transformedTarget = resolveTargetOfAnAssignment componentObject contextOfStatement target
                    let transformedExpression = transformMMExpressionInsideAComponentToSimpleExpression fieldCache componentObject expression
                    let transformedAssignment = SimpleStatement.AssignmentStatement (transformedTarget,transformedExpression)
                    let newToTransform = toTransform.Tail
                    transformMMStepInfosToSimpleStatements fieldCache methodBodyResolver (collected @ [transformedAssignment]) newToTransform
    
    
    // module (the public part for _external_ use)

    //TODO: Put methodBodyResolver into cached information and use Cached Information here
    //      This function also needs the SimpleGlobalFieldCache and RootComponentCache
    member this.partitionUpdateInSimpleStatements (partition:MMPartitionObject) : SimpleStatement list=
        //TODO: sort, updateMethods of Non-Root-Components
        //partition.RootComponent 
        let collected = []
        let toTransform =
            let contextOfCurrentPartitionRootComponent = contextCache.createContextOfRootComponent partition
            {
                MMStepInfo.context= contextOfCurrentPartitionRootComponent;
                MMStepInfo.componentObject = partition.RootComponent;
                MMStepInfo.statement=(configuration.MethodBodyResolver.Item (partition.RootComponent.ComponentSymbol,partition.RootComponent.ComponentSymbol.UpdateMethod));
            }
        let partitionUpdateInSimpleStatements = transformMMStepInfosToSimpleStatements fieldCache configuration.MethodBodyResolver collected [toTransform]
        partitionUpdateInSimpleStatements

    member this.getSimpleGlobalFields : SimpleGlobalField list =
            fieldCache.getSimpleGlobalFields
                           
    member this.resolveFieldAccessInsideAFormula (referenceSymbol:MMComponentReferenceSymbol) (field:MMFieldSymbol) : SimpleGlobalField =
        fieldCache.resolveFieldAccessInsideAFormula referenceSymbol field