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
namespace SafetySharp.Internal.Modelchecking

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

type internal MMModelObject = SafetySharp.Internal.Metamodel.ModelObject
type internal MMPartitionObject = SafetySharp.Internal.Metamodel.PartitionObject
type internal MMComponentObject = SafetySharp.Internal.Metamodel.ComponentObject
type internal MMFieldObject = SafetySharp.Internal.Metamodel.FieldObject
type internal MMConfiguration = SafetySharp.Internal.Metamodel.Configuration // <--------- main artifact
      
type internal MMTypeSymbol = SafetySharp.Internal.Metamodel.TypeSymbol
type internal MMFieldSymbol = SafetySharp.Internal.Metamodel.FieldSymbol
type internal MMLocalSymbol = SafetySharp.Internal.Metamodel.LocalSymbol
type internal MMParameterSymbol = SafetySharp.Internal.Metamodel.ParameterSymbol
type internal MMMethodSymbol = SafetySharp.Internal.Metamodel.MethodSymbol
type internal MMProvidedPortSymbol = SafetySharp.Internal.Metamodel.ProvidedPortSymbol
type internal MMRequiredPortSymbol = SafetySharp.Internal.Metamodel.RequiredPortSymbol
type internal MMComponentReferenceSymbol = SafetySharp.Internal.Metamodel.ComponentReferenceSymbol
type internal MMComponentSymbol = SafetySharp.Internal.Metamodel.ComponentSymbol
type internal MMPartitionSymbol = SafetySharp.Internal.Metamodel.PartitionSymbol
type internal MMModelSymbol = SafetySharp.Internal.Metamodel.ModelSymbol
      
type internal MMExpression = SafetySharp.Internal.Metamodel.Expression
type internal MMUnaryOperator = SafetySharp.Internal.Metamodel.UnaryOperator
type internal MMBinaryOperator = SafetySharp.Internal.Metamodel.BinaryOperator
type internal MMStatement = SafetySharp.Internal.Metamodel.Statement
type internal MMFormula = SafetySharp.Internal.Metamodel.Formula
type internal MMUnaryFormulaOperator = SafetySharp.Internal.Metamodel.UnaryFormulaOperator
type internal MMBinaryFormulaOperator = SafetySharp.Internal.Metamodel.BinaryFormulaOperator
type internal MMMethodBodyResolver = Map<MMComponentSymbol * MMMethodSymbol, MMStatement>


// TODO: Ensure reverse mapping is working for debugging purposes
//       Traceability: Introduce a element, which allows it to connect SimpleExpressions with MMExpressions. Three ways to achieve this
//       - Duplicate every discriminated union case of SimpleStatement, SimpleExpression, SimpleGlobalField to allow the case
//         that the field is artificial or references a MM-equivalent
//              (contra: bloats types)
//       - Introduce a mapping <----- switch to this solution
//              (contra: bloats recursive call parameters and return parameters. But could also be a mutable map in the Type. This is contrary to the functional programming style)
//       - Introduce in every discriminated union case an optional element
//              (contra: drag along information not really necessary in many cases)
//       - Introduce one extra case: "MMReference of MMX * SimpleX" and member-Functions "dereference" and "recursiveDereference"


// Maybe TODO:
// The Simplified Metamodel is still connected to the Full Metamodel, because it links to some of its artifacts
// (Context uses MMComponentObject,SimpleExpression knows MMComponentObject...). If we get rid of it and replace it with a simple mapping, the Simplified
// Metamodel is completly independent of the Full Metamodel, testing is easier. Until now we don't really need it. This keeps the code smaller and less redundancy.

// TODO: Move much of the stuff into file SimplifiedMetamodel

//TODO: Also use in Context
type internal SimplePartitionIdentity = {
     RootComponentName : string;
}

type internal ReverseComponentObjectMap = Map<string,MMComponentReferenceSymbol>

//TODO: Switch from RootComponentName to SimplePartition. Or maybe not (to avoid cyclic dependencies)
type internal Context = {
    // HierarchicalAccess does not contain the name of the root Component.
    // There are different cases how the hierarchical access is generated
    // Case 1: FromComponentFields: Generated from Field of a Component (Method names do not overlap with fields in a component.)
    //      Last object is the name of the root-Component; head is a subComponent of its parent:  subComponent1::(parentOfSubComponent1)*.
    //      Construction is done in type SimpleGlobalFieldCache
    // TODO: In progress
    // Case 2: FromMethods: Generated as Local Field or Parameter of a RequiredPort or an Update (They do not overlap. But they may overlap with local fields)
    //      Head is method name without parameters (e.g. Update). Rest of the list is the component hierarchy as in case 1
    // TODO:
    // Case 3: FromBindings: Generated by a Required-Ports
    //      Head is the hierarchy of the component name as in case 1. Method name is not used, because an artificial name is constructed
    //      for the FieldSymbol with the method name of the port.
    HierarchicalAccess : string list;
    //only the name of the root component
    Partition : SimplePartitionIdentity; 
}

type internal SimpleConstLiteral = 
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

type internal SimpleFieldSymbol = {
    /// The name of the field. Field names are unique within a context
    Name : string
    /// The type of the field.
    Type : MMTypeSymbol
} with
    static member standardInitialValueOfType (_type : MMTypeSymbol) =
        match _type with
            | MMTypeSymbol.Boolean -> SimpleConstLiteral.BooleanLiteral(false)
            | MMTypeSymbol.Integer -> SimpleConstLiteral.IntegerLiteral(0)
            | MMTypeSymbol.Decimal -> SimpleConstLiteral.DecimalLiteral(0.0f |> decimal)



[<StructuralEquality;StructuralComparison>]
type internal SimpleGlobalFieldWithContext = {
    Context : Context;
    FieldSymbol: SimpleFieldSymbol;
    InitialValues : SimpleConstLiteral list;
} with
    member this.createDerivedFieldWithStandardValues (postfixCounter:int) = 
        let initialValue = SimpleFieldSymbol.standardInitialValueOfType this.FieldSymbol.Type 
        let newFieldSymbol =            
            {
                SimpleFieldSymbol.Name=this.FieldSymbol.Name+postfixCounter.ToString();
                SimpleFieldSymbol.Type= this.FieldSymbol.Type;
            }
        {
            SimpleGlobalFieldWithContext.Context=this.Context;
            SimpleGlobalFieldWithContext.FieldSymbol=newFieldSymbol;
            SimpleGlobalFieldWithContext.InitialValues=[initialValue];
        }

// TODO: - Remove FieldOfMetamodel, add different Cases of context in Context (the context object is also used when the
//         linearizer walks through the components and methods
//       - Replace Usage of SimpleGlobalFieldWithContext in maps by SimpleGlobalField where practicable 
//       - Transform it into a record-type, if no different case is found. But: It might be the case, that we
//         introduce complete artificial fields which optimize things. Maybe better keep it
//       - Add Attributes
//[<StructuralEquality;StructuralComparison>]
type internal SimpleGlobalField =
    | FieldWithContext of Field : SimpleGlobalFieldWithContext
    //| FieldOfMetamodel of ComponentObject : MMComponentObject * Field : SimpleGlobalField 
    with
        member this.getFieldSymbol =
            match this with
                | SimpleGlobalField.FieldWithContext (field)-> field.FieldSymbol
                //| SimpleGlobalField.FieldOfMetamodel (_,field)-> field.getFieldSymbol
        member this.getInitialValues =
            match this with
                | SimpleGlobalField.FieldWithContext (field)-> field.InitialValues
                //| SimpleGlobalField.FieldOfMetamodel (_,field)-> field.getInitialValues
        member this.hasContext =
            match this with
                | SimpleGlobalField.FieldWithContext _ -> true
                //| SimpleGlobalField.FieldOfMetamodel (_,field) -> field.hasContext
        member this.getContext =
            match this with
                | SimpleGlobalField.FieldWithContext (field) -> field.Context
                //| SimpleGlobalField.FieldOfMetamodel (_,field) -> field.getContext
        member this.getSimpleGlobalFieldWithContext =
            match this with
                | SimpleGlobalField.FieldWithContext (field) -> field
                //| SimpleGlobalField.FieldOfMetamodel (_,field) -> field.getSimpleGlobalFieldWithContext


// A SimpleExpression knows the Context of its variables (We use MMExpression, because it already offers this functionality for Formulas)
type internal SimpleExpression = 
    /// Represents a constant value which may be e.g. a BooleanLiteral with the values true and false.
    | ConstLiteral of Value : SimpleConstLiteral
    
    /// Represents the application of an unary operator to an expression.
    | UnaryExpression of Operand : SimpleExpression * Operator : MMUnaryOperator

    /// Represents the application of a binary operator to two subexpressions.
    | BinaryExpression of LeftExpression : SimpleExpression * Operator : MMBinaryOperator * RightExpression : SimpleExpression

    /// Represents a field access, either for reading or writing.
    | FieldAccessExpression of Field : SimpleGlobalField



// A simpleStatement has only assignments and guarded commands. Also Assignments are defined on SimpleGlobalFields
type internal SimpleStatement = 
    | GuardedCommandStatement of (SimpleExpression * (SimpleStatement list) ) list //Guard (which knows its Context) * Statements
    | AssignmentStatement of Target : SimpleGlobalField * Expression : SimpleExpression //Expression (knows its Context). SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)


        
type internal ContextCache (configuration:MMConfiguration) =
        // _once_ calculated and cached information for internal use
        let model = configuration.ModelObject

        let rootComponentToPartition : Map<string,SimplePartitionIdentity> =
            let counter = ref 0
            model.Partitions |> List.map (fun elem -> elem.RootComponent)
                             |> List.map (fun elem -> counter:=!counter+1
                                                      let counterString = (!counter).ToString()
                                                      let partition = {SimplePartitionIdentity.RootComponentName="root"+counterString;}
                                                      (elem.Name,partition))
                             |> Map.ofList

        //TODO: Make creation more efficient
        let partitionToPartitionObject : Map<SimplePartitionIdentity,MMPartitionObject> =
            let findComponent (internalName:string) : MMPartitionObject =
                model.Partitions |> List.find (fun elem  -> elem.RootComponent.Name = internalName)
            rootComponentToPartition |> Map.toList
                                     |> List.map (fun (internalName,artificialName) -> (artificialName,findComponent internalName))
                                     |> Map.ofList

        // accessor and helper functions (internal use)
        let partitionOfRootComponent (rootComponent:MMComponentObject) : SimplePartitionIdentity =
            rootComponentToPartition.Item rootComponent.Name
            
        // accessor and helper functions (external use)
        member this.createContextOfRootComponent (partition:MMPartitionObject) : Context =
            {
                Context.HierarchicalAccess = [];
                Context.Partition = partitionOfRootComponent partition.RootComponent;
            }
        member this.createContextForSubcomponent (parentContext:Context) (newElementName:string) (comp:MMComponentObject) : Context =
            {
                Context.HierarchicalAccess = newElementName::parentContext.HierarchicalAccess; //parentsAndMe
                Context.Partition = parentContext.Partition;
            }

        // TODO: createContextForMethod()

        member this.getPartitions : SimplePartitionIdentity list =
            rootComponentToPartition |> Map.toList
                                     |> List.map (fun (_,value) -> value)
        
        // name is the artificial name
        member this.getRootComponentFromPartition (paritition:SimplePartitionIdentity) : MMPartitionObject =
            partitionToPartitionObject.Item paritition

        
    // this is extraced from ModelInformationCache, to keep the code together which belongs together
    // TODO: Sort and categorize:
    //      - _once_ calculated and cached information for internal use
    //      - _once_ calculated and cached information for external use (better write accessor functions for it)        
    //      - accessor and helper functions (internal use)
    //      - accessor and helper functions (external use)
type internal SimpleGlobalFieldCache (contextCache:ContextCache, configuration:MMConfiguration) =
        // this should only calculate and _cache_ information for the transformation to
        // SimpleStatements/SimpleExpressions and not be used from outside this file
        let model = configuration.ModelObject
        
        let simpleFieldSymbolFromMMFieldSymbol (_symbol:MMFieldSymbol) =
            {
                SimpleFieldSymbol.Name = _symbol.Name;
                SimpleFieldSymbol.Type = _symbol.Type;
            }

        let simpleFieldSymbolFromMMLocalSymbol (_symbol:MMLocalSymbol) =
            {
                SimpleFieldSymbol.Name = _symbol.Name;
                SimpleFieldSymbol.Type = _symbol.Type;
            }
        let simpleFieldSymbolFromMMParameterSymbol (_symbol:MMParameterSymbol) =
            {
                SimpleFieldSymbol.Name = _symbol.Name;
                SimpleFieldSymbol.Type = _symbol.Type;
            }
        
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

        // Map<string*string,SimpleGlobalField> first string is the unique componentName, second string is fieldName
        let simpleGlobalFieldFromFieldInAComponentMap : Map<string*string,SimpleGlobalField> ref = 
            ref Map.empty<string*string,SimpleGlobalField>

        // has side-effect, so should only be executed once
        let simpleGlobalFieldsFromComponentFields : SimpleGlobalField list =
            let appendFieldInAComponentToMap (uniqueComponentName:string) (fieldName:string) (simpleGlobalFieldToAdd:SimpleGlobalField) =
                simpleGlobalFieldFromFieldInAComponentMap := simpleGlobalFieldFromFieldInAComponentMap.Value.Add((uniqueComponentName,fieldName),simpleGlobalFieldToAdd)
            // It traverses the model and generates a list of all fields with all necessary information about the field (SimpleGlobalField)
            // This function works like this: collectFromPartition -> collectFromComponent -> collectFieldInComponent
            let rec collectFromComponent (componentObject:MMComponentObject) (myContext:Context) : SimpleGlobalField list =
                let collectedInSubcomponents : SimpleGlobalField list =
                    (getSubComponentObjects componentObject.Subcomponents) |> List.collect (fun (name,comp) -> collectFromComponent comp (contextCache.createContextForSubcomponent myContext name comp) )
                let collectFieldInComponent (fieldobject:MMFieldObject) =
                    let fieldContext = {
                        SimpleGlobalFieldWithContext.Context=myContext;
                        SimpleGlobalFieldWithContext.FieldSymbol=simpleFieldSymbolFromMMFieldSymbol fieldobject.FieldSymbol;
                        SimpleGlobalFieldWithContext.InitialValues=(SimpleConstLiteral.convertFromObjectList fieldobject.InitialValues);
                    }
                    let newField = SimpleGlobalField.FieldWithContext(fieldContext)
                    //add to map
                    appendFieldInAComponentToMap componentObject.Name fieldobject.FieldSymbol.Name newField
                    // return for the collector
                    newField
                let collectedInThisComponent = (getFieldObjects componentObject.Fields) |> List.map collectFieldInComponent 
                collectedInThisComponent @ collectedInSubcomponents
            let collectFromPartition (partition:MMPartitionObject) : SimpleGlobalField list  =
                let contextOfCurrentPartitionRootComponent = contextCache.createContextOfRootComponent partition
                collectFromComponent partition.RootComponent contextOfCurrentPartitionRootComponent
            model.Partitions |> List.collect collectFromPartition
        
        // for faster access
        let simpleGlobalFieldsFromComponentFieldsSet = Set.ofList simpleGlobalFieldsFromComponentFields
        
        
        // Map<string*string,SimpleGlobalField> first string is the unique componentName, second string is methodname, third string is fieldName
        let simpleGlobalFieldFromFieldOrParameterInAMethodMap : Map<string*string*string,SimpleGlobalField> ref = 
            ref Map.empty<string*string*string,SimpleGlobalField>
            
        // has side-effect, so should only be executed once
        let simpleGlobalFieldsFromMethods : SimpleGlobalField list =
            let appendFieldInAMethodToMap (uniqueComponentName:string) (methodName:string) (fieldName:string) (simpleGlobalFieldToAdd:SimpleGlobalField) =
                simpleGlobalFieldFromFieldOrParameterInAMethodMap := simpleGlobalFieldFromFieldOrParameterInAMethodMap.Value.Add((uniqueComponentName,methodName,fieldName),simpleGlobalFieldToAdd)
            // It traverses the model and generates a list of all fields with all necessary information about the field (SimpleGlobalField)
            // This function works like this: collectFromPartition -> collectFromComponent -> collectFromMethod -> collectFieldInMethod/collectParameterOfMethod
            let rec collectFromComponent (componentObject:MMComponentObject) (myContext:Context) : SimpleGlobalField list =
                
                ////CONTEXT!=!=!=!=!=!=!!=
                
                
                let collectedInSubcomponents : SimpleGlobalField list =
                    (getSubComponentObjects componentObject.Subcomponents) |> List.collect (fun (name,comp) -> collectFromComponent comp (contextCache.createContextForSubcomponent myContext name comp) )
                let collectFromMethod (methodSymbol:MMMethodSymbol) : SimpleGlobalField list =
                    let collectLocalFieldInMethod (localSymbol:MMLocalSymbol) =
                        let fieldContext = {
                            SimpleGlobalFieldWithContext.Context=myContext;
                            SimpleGlobalFieldWithContext.FieldSymbol=simpleFieldSymbolFromMMLocalSymbol localSymbol;
                            SimpleGlobalFieldWithContext.InitialValues=([SimpleFieldSymbol.standardInitialValueOfType localSymbol.Type]);
                        }
                        let newField = SimpleGlobalField.FieldWithContext(fieldContext)
                        //add to map
                        appendFieldInAMethodToMap componentObject.Name methodSymbol.Name localSymbol.Name newField
                        // return for the collector
                        newField
                    let collectParameterOfMethod (parameterSymbol:MMParameterSymbol) =
                        let fieldContext = {
                            SimpleGlobalFieldWithContext.Context=myContext;
                            SimpleGlobalFieldWithContext.FieldSymbol=simpleFieldSymbolFromMMParameterSymbol parameterSymbol;
                            SimpleGlobalFieldWithContext.InitialValues=([SimpleFieldSymbol.standardInitialValueOfType parameterSymbol.Type]);
                        }
                        let newField = SimpleGlobalField.FieldWithContext(fieldContext)
                        //add to map
                        appendFieldInAMethodToMap componentObject.Name methodSymbol.Name parameterSymbol.Name newField
                        // return for the collector
                        newField
                    let methodFields = methodSymbol.Locals |> List.map collectLocalFieldInMethod
                    let methodParameters = methodSymbol.Parameters |> List.map collectParameterOfMethod
                    methodFields @ methodParameters
                let methodSymbols =
                    let fromUpdate = componentObject.ComponentSymbol.UpdateMethod
                    let fromProvidedPorts =
                        let getMethodSymbol (port:MMProvidedPortSymbol) = 
                            match port with
                                | MMProvidedPortSymbol.ProvidedPort methodSymbol -> methodSymbol
                        componentObject.ComponentSymbol.ProvidedPorts |> List.map getMethodSymbol
                    fromUpdate::fromProvidedPorts
                let collectedInThisComponent = methodSymbols |> List.collect collectFromMethod 
                collectedInThisComponent @ collectedInSubcomponents
            let collectFromPartition (partition:MMPartitionObject) : SimpleGlobalField list  =
                let contextOfCurrentPartitionRootComponent = contextCache.createContextOfRootComponent partition
                collectFromComponent partition.RootComponent contextOfCurrentPartitionRootComponent
            model.Partitions |> List.collect collectFromPartition

        // for faster access
        let simpleGlobalFieldsFromMethodsSet = Set.ofList simpleGlobalFieldsFromMethods
        
        // has side-effect, so should only be executed once
        let simpleGlobalFieldsFromBindings : SimpleGlobalField list =
            //TODO
            []

        // for faster access
        let simpleGlobalFieldsFromBindingsSet = Set.ofList simpleGlobalFieldsFromBindings
                  
        member this.resolveFieldAccessInsideAComponent (comp:MMComponentObject) (field:MMFieldSymbol) : SimpleGlobalField =
            let componentObjectName = comp.Name
            let fieldName = field.Name
            simpleGlobalFieldFromFieldInAComponentMap.Value.Item (componentObjectName,fieldName)

        
        member this.createSimpleFieldAccessExpression (field:MMFieldSymbol) (comp:MMComponentObject): SimpleExpression =
            let componentReference = ComponentObjectToComponentReference comp
            let simpleGlobalField = this.resolveFieldAccessInsideAFormula componentReference field
            SimpleExpression.FieldAccessExpression(simpleGlobalField)

        member this.getSimpleGlobalFields : SimpleGlobalField list =
            simpleGlobalFieldsFromComponentFields @ simpleGlobalFieldsFromMethods @ simpleGlobalFieldsFromBindings

        member this.isFieldInAComponent (field:SimpleGlobalField) =
            simpleGlobalFieldsFromComponentFieldsSet.Contains field
                           
        member this.resolveFieldAccessInsideAFormula (referenceSymbol:MMComponentReferenceSymbol) (field:MMFieldSymbol) : SimpleGlobalField =
            let componentObject = model.ComponentObjects.Item referenceSymbol
            let componentObjectName = componentObject.Name
            let fieldName = field.Name
            simpleGlobalFieldFromFieldInAComponentMap.Value.Item (componentObjectName,fieldName)
        
    
    
    
// Many steps are a sequence. Only use in this file
type internal MMStepInfo = {
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

type internal MetamodelToSimplifiedMetamodel (configuration:MMConfiguration) =
    let contextCache = ContextCache(configuration)
    let fieldCache = SimpleGlobalFieldCache(contextCache,configuration)

    let resolveTargetOfAnAssignment (componentObject:MMComponentObject) (context:Context) (field:MMFieldSymbol) : SimpleGlobalField =
        fieldCache.resolveFieldAccessInsideAComponent componentObject field
    
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
            | MMExpression.ReadField (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    fieldCache.createSimpleFieldAccessExpression field comp
                else
                    //called inside a formula or already transformed
                    failwith "Use transformExpressionInsideAComponent only for expression inside untransformed components and not in formulas"
            | MMExpression.ReadLocal (local:MMLocalSymbol) ->
                failwith "NotImplementedYet"
            | MMExpression.ReadParameter (parameter:MMParameterSymbol) ->
                failwith "NotImplementedYet"

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
                    // Also: Reset values of temporary fields which are only accessible in the current scope
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

                | MMStatement.WriteField (target : MMFieldSymbol, expression : MMExpression) ->
                    let transformedTarget = resolveTargetOfAnAssignment componentObject contextOfStatement target
                    let transformedExpression = transformMMExpressionInsideAComponentToSimpleExpression fieldCache componentObject expression
                    let transformedAssignment = SimpleStatement.AssignmentStatement (transformedTarget,transformedExpression)
                    let newToTransform = toTransform.Tail
                    transformMMStepInfosToSimpleStatements fieldCache methodBodyResolver (collected @ [transformedAssignment]) newToTransform
                | MMStatement.WriteLocal (local:MMLocalSymbol,expression:MMExpression) ->
                    failwith "NotImplementedYet"
                | MMStatement.WriteParameter (parameter:MMParameterSymbol, expression:MMExpression) ->
                    failwith "NotImplementedYet"

                    

    
    
    // module (the public part for _external_ use)

    //TODO: Put methodBodyResolver into cached information and use Cached Information here
    //      This function also needs the SimpleGlobalFieldCache and RootComponentCache
    member this.partitionUpdateInSimpleStatements2 (partition:MMPartitionObject) : SimpleStatement list=
        //TODO: sort, updateMethods of Non-Root-Components
        //partition.RootComponent 
        let collected = []
        let toTransform =
            let contextOfCurrentPartitionRootComponent = contextCache.createContextOfRootComponent partition
            {
                MMStepInfo.context= contextOfCurrentPartitionRootComponent;
                MMStepInfo.componentObject = partition.RootComponent;
                MMStepInfo.statement=
                    match partition.RootComponent.ComponentSymbol.UpdateMethod with
                    | None -> MMStatement.EmptyStatement
                    | Some methodSymbol -> (configuration.MethodBodyResolver.Item (partition.RootComponent.ComponentSymbol,methodSymbol));
            }
        let partitionUpdateInSimpleStatements = transformMMStepInfosToSimpleStatements fieldCache configuration.MethodBodyResolver collected [toTransform]
        partitionUpdateInSimpleStatements

    //TODO: Refactor PromelaTransform to use this function
    member this.partitionUpdateInSimpleStatements (partition:SimplePartitionIdentity) : SimpleStatement list =
        let mmpartitionObject = contextCache.getRootComponentFromPartition partition
        this.partitionUpdateInSimpleStatements2 mmpartitionObject

    member this.getPartitions : SimplePartitionIdentity list =
        contextCache.getPartitions

    member this.getSimpleGlobalFields : SimpleGlobalField list =
        fieldCache.getSimpleGlobalFields

    member this.isFieldInAComponent (field:SimpleGlobalField) =
            fieldCache.isFieldInAComponent field
                           
    member this.resolveFieldAccessInsideAFormula (referenceSymbol:MMComponentReferenceSymbol) (field:MMFieldSymbol) : SimpleGlobalField =
        fieldCache.resolveFieldAccessInsideAFormula referenceSymbol field