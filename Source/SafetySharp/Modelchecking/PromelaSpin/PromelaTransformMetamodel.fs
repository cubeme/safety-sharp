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

namespace SafetySharp.Modelchecking.PromelaSpin

open PromelaAstHelpers

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

type PrExpression = SafetySharp.Modelchecking.PromelaSpin.AnyExpr
type PrConst = SafetySharp.Modelchecking.PromelaSpin.Const
type PrUnarop = SafetySharp.Modelchecking.PromelaSpin.Unarop
type PrBinarop = SafetySharp.Modelchecking.PromelaSpin.Binarop
type PrAndor = SafetySharp.Modelchecking.PromelaSpin.Andor
type PrStatement = SafetySharp.Modelchecking.PromelaSpin.Stmnt
type PrOptions = SafetySharp.Modelchecking.PromelaSpin.Options
type PrSequence = SafetySharp.Modelchecking.PromelaSpin.Sequence
type PrStep = SafetySharp.Modelchecking.PromelaSpin.Step
type PrFormula = SafetySharp.Modelchecking.PromelaSpin.Formula
type PrBinaryFormulaOperator = SafetySharp.Modelchecking.PromelaSpin.BinaryFormulaOperator
type PrUnaryFormulaOperator = SafetySharp.Modelchecking.PromelaSpin.UnaryFormulaOperator
type PrVarref = SafetySharp.Modelchecking.PromelaSpin.Varref
type PrProctype = SafetySharp.Modelchecking.PromelaSpin.Proctype
type PrDeclLst = SafetySharp.Modelchecking.PromelaSpin.DeclLst
type PrModule = SafetySharp.Modelchecking.PromelaSpin.Module
type PrOneDecl = SafetySharp.Modelchecking.PromelaSpin.OneDecl
type PrTypename = SafetySharp.Modelchecking.PromelaSpin.Typename
type PrIvar = SafetySharp.Modelchecking.PromelaSpin.Ivar
type PrAssign = SafetySharp.Modelchecking.PromelaSpin.Assign
type PrSpec = SafetySharp.Modelchecking.PromelaSpin.Spec

type ReverseComponentObjectMap = Map<string,MMComponentReferenceSymbol>

type Context = {
    //partition : MMPartitionObject;
    container : MMComponentObject;
    hierarchicalAccess : string list; //last object is the name of the root-Component; head is a subComponent of its parent:  subComponent1(::parentOfSubComponent1)*::rootComponent. Construction is done in "collectFields"
}

type FieldInfo = {
    context : Context;
    field : MMFieldObject; //TODO: maybe switch to MMFieldSymbol. Cannot find any advantage of using MMFieldObject yet
}

type ResolverForFieldInfos = Map<string*string,FieldInfo>

// many steps are a sequence
type MMStepInfo = {
    context : Context;
    statement : MMStatement;
}

// A SimpleExpression knows the Context of its variables (MMExpression already offers this functionality for Formulas)
type SimpleExpression = MMExpression 
// A simpleStatement has only assignments and guarded commands. Also Assignments are defined on fieldinfos
// TODO: Maybe remove Context and use expression of a formula which knows its MMComponentObject directly
type SimpleStatement = 
    | GuardedCommandStatement of (SimpleExpression * (SimpleStatement list) ) list //Guard (which knows its Context) * Statements
    | AssignmentStatement of Target : FieldInfo * Expression : SimpleExpression //Expression (knows its Context). FieldInfo has its own Context (may result of a return-Statement, when context is different)


           
type MetamodelToPromela (model : MMModelObject) =    

    let getSubComponentObjects (subcomponentMap : Map<MMComponentReferenceSymbol, MMComponentObject>) : ((string*MMComponentObject) list) =
        subcomponentMap |> Map.fold (fun acc key value -> (key.Name,value)::acc) []
    
    let getFieldObjects (fieldMap : Map<MMFieldSymbol, MMFieldObject>) : (MMFieldObject list) =
        fieldMap |> Map.fold (fun acc key value -> value::acc) []

    let reverseComponentObjects : ReverseComponentObjectMap =
        // string is the unique name of the ComponentObject 
        // ReverseComponentObjectMap = Map<string,MMComponentReferenceSymbol>      
        model.ComponentObjects |> Map.toList
                               |> List.map (fun (reference,compobject) -> (compobject.Name,reference))
                               |> Map.ofList

    let ComponentObjectToComponentReference (comp:MMComponentObject) : MMComponentReferenceSymbol =
        reverseComponentObjects.Item comp.Name

    let rootComponentToName : Map<string,string> =
        let counter = ref 0
        model.Partitions |> List.map (fun elem -> elem.RootComponent)
                         |> List.map (fun elem -> counter:=!counter+1
                                                  let counterString = (!counter).ToString()
                                                  (elem.Name,"root"+counterString))
                         |> Map.ofList

    let fieldInfos : FieldInfo list =
        // This function works like this: collectFromPartition -> collectFromComponent -> collectFieldInThisComponent
        // It traverses the model and generates a list of all fields with all necessary information about the field (FieldInfo)
        let rec collectFromComponent (parentsAndMe:string list) (comp:MMComponentObject) : FieldInfo list =             
            let collectedInSubcomponents : FieldInfo list =
                (getSubComponentObjects comp.Subcomponents) |> List.collect (fun (name,comp) -> collectFromComponent (name::parentsAndMe) comp)
            let collectFieldInThisComponent (fieldobject:MMFieldObject) =
                {
                    FieldInfo.context = {
                                            Context.container = comp;
                                            Context.hierarchicalAccess = parentsAndMe;
                                        }
                    FieldInfo.field = fieldobject;
                }
            let collectedInThisComponent = (getFieldObjects comp.Fields) |> List.map collectFieldInThisComponent 
            collectedInThisComponent @ collectedInSubcomponents
        let collectFromPartition (partition:MMPartitionObject) : FieldInfo list  =
            let nameOfRoot= rootComponentToName.Item partition.RootComponent.Name
            collectFromComponent [nameOfRoot] partition.RootComponent
        model.Partitions |> List.collect collectFromPartition
        
    let resolverForFieldInfos : ResolverForFieldInfos = 
        //type ResolverForFormulas = Map<string*string,FieldInfo> first string is the unique componentName, second string is fieldName
        fieldInfos |> List.map (fun elem -> (elem.context.container.Name, elem.field.FieldSymbol.Name),elem)
                   |> Map.ofList
                   
    let resolveFieldAccessInsideAFormula (referenceSymbol:MMComponentReferenceSymbol) (field:MMFieldSymbol) : FieldInfo =
        let componentObject = model.ComponentObjects.Item referenceSymbol
        let componentObjectName = componentObject.Name
        let fieldName = field.Name
        resolverForFieldInfos.Item (componentObjectName,fieldName)
        
    let resolveFieldAccessInsideAComponent (comp:MMComponentObject) (field:MMFieldSymbol) : FieldInfo =
        let componentObjectName = comp.Name
        let fieldName = field.Name
        resolverForFieldInfos.Item (componentObjectName,fieldName)


    let rec resolveTargetOfAnAssignment (context:Context) (expression:MMExpression) : FieldInfo =
        // Use resolveFieldInfoInCode only for expression inside components and not in formulas
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
                    {
                        FieldInfo.context=context;
                        FieldInfo.field = (context.container.Fields.Item field);
                    }
        
    let rec transformMMExpressionInsideAComponentToSimpleExpression (comp:MMComponentObject) (expression:MMExpression) : SimpleExpression =
        match expression with
            | MMExpression.BooleanLiteral (value:bool) -> SimpleExpression.BooleanLiteral(value)
            | MMExpression.IntegerLiteral (value:int) ->  SimpleExpression.IntegerLiteral(value)
            | MMExpression.DecimalLiteral (value:decimal) -> failwith "NotImplementedYet"
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                let transformedOperand = transformMMExpressionInsideAComponentToSimpleExpression comp operand
                SimpleExpression.UnaryExpression(transformedOperand,operator)
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                let transformedLeft = transformMMExpressionInsideAComponentToSimpleExpression comp leftExpression
                let transformedRight = transformMMExpressionInsideAComponentToSimpleExpression comp rightExpression
                SimpleExpression.BinaryExpression(transformedLeft,operator,transformedRight)
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    MMExpression.FieldAccessExpression(field,Some(ComponentObjectToComponentReference comp))
                else
                    //called inside a formula or already transformed
                    failwith "Use transformExpressionInsideAComponent only for expression inside untransformed components and not in formulas"

    let rec transformMMStepInfosToSimpleStatements (methodBodyResolver:MMMethodBodyResolver) (collected:SimpleStatement list) (toTransform:MMStepInfo list) : SimpleStatement list =
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
            let contextOfStatement = firstItem.context

            match statementToProcess with
                | MMStatement.EmptyStatement ->
                    let newToTransform = toTransform.Tail
                    transformMMStepInfosToSimpleStatements methodBodyResolver collected newToTransform
                | MMStatement.BlockStatement (statements : MMStatement list) ->
                    let coverStatementWithContext (statement:MMStatement) =
                        {
                            MMStepInfo.context=contextOfStatement;
                            MMStepInfo.statement=statement;
                        }
                    let expandedBlockStatement = statements |> List.map coverStatementWithContext
                    let newToTransform = expandedBlockStatement @ toTransform.Tail
                    transformMMStepInfosToSimpleStatements methodBodyResolver collected newToTransform
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
                    failwith "NotImplementedYet"
                    (*let transformGuardedStmnt ((guard,stmnt):MMExpression * MMStatement) =
                        let transformedGuard = this.transformExpression guard
                        let transformedStmnt = this.transformStatement stmnt
                        PrSequence.Sequence([anyExprToStep transformedGuard;stmntToStep transformedStmnt])
                    guardedStmnts |> List.map transformGuardedStmnt
                                    |> (fun sequences -> PrStatement.IfStmnt(PrOptions.Options(sequences)))*)
                | MMStatement.AssignmentStatement (target : MMExpression, expression : MMExpression) ->
                    //resolveTargetOfAnAssignment
                    let target = resolveTargetOfAnAssignment target
                    failwith "NotImplementedYet"
            
    // build (toTransform:MMStepInfo list) with all updates in the correct order
    // let collectPartitionUpdateSequence =
    //      TODO
    //   - Only updates, no bindings
    //   - TODO: Updates are proccessed in the correct order

    member this.transformFieldInfoToName (fieldInfo : FieldInfo) =
        //TODO: Besides compName+fieldName is something unique inside the model we cannot. But it is not guaranteed the name is readable or even supported by the model checker 
        // so write a method to find a better name.
        // this is something model checker specific, as different model checkers may have different constraints for identifier
        //let partitionName = "pA" //partition has no name, use A as dummy. TODO: find something better
        let hierarchicalAccessName =
            fieldInfo.context.hierarchicalAccess |> List.rev //the order should be root::subcomponent::leafSubcomponent
                                                 |> List.map (fun elem -> "c"+elem) //add c in front of every element
                                                 |> String.concat "_"
        let fieldName = "_f"+fieldInfo.field.FieldSymbol.Name
        sprintf "%s%s" hierarchicalAccessName fieldName

    member this.transformFieldInfoToVarref (fieldInfo : FieldInfo) =
        let varName = this.transformFieldInfoToName fieldInfo
        PrVarref.Varref(varName,None,None)
    
    member this.generateFieldDeclarations (fields : FieldInfo list) : PrModule =
        let generateDecl (field:FieldInfo) : PrOneDecl =
            let _type = match field.field.FieldSymbol.Type with
                            | MMTypeSymbol.Boolean -> PrTypename.Bool
                            | MMTypeSymbol.Integer -> PrTypename.Int
                            | MMTypeSymbol.Decimal -> failwith "NotImplementedYet"
            let _varName = this.transformFieldInfoToName field
            let _variable = PrIvar.Ivar(_varName,None,None)
            PrOneDecl.OneDecl(None,_type,[_variable])
        fields |> List.map generateDecl
               |> PrDeclLst.DeclLst
               |> PrModule.GlobalVarsAndChans

    member this.generateFieldInitialisations (fields : FieldInfo list) : PrStatement list =
        let generateInit (field:FieldInfo) : PrStatement =
            let generateSequence (initialValue : obj) : PrSequence =
                let assignVarref = this.transformFieldInfoToVarref field
                let assignExpr =
                    match initialValue with
                        | :? int as value -> PrExpression.Const(PrConst.Number(value))
                        | :? bool as value -> match value with
                                                | true  -> PrExpression.Const(PrConst.True)
                                                | false -> PrExpression.Const(PrConst.False)
                        | _ -> failwith "NotImplementedYet"
                //also possible to add a "true" as a guard to the returned sequence
                statementsToSequence [PrStatement.AssignStmnt(PrAssign.AssignExpr(assignVarref,assignExpr))]
                
            field.field.InitialValues |> List.map generateSequence
                                      |> PrOptions.Options
                                      |> PrStatement.IfStmnt
        fields |> List.map generateInit
    
    member this.generatePartitionUpdateCode (partition) =
        []

    member this.generatePartitionBindingCode =
        ""
    
    // THIS IS THE MAIN FUNCTION AND ENTRY POINT
    member this.transformConfiguration (configuration:MMConfiguration) : PrSpec =
        let varModule = this.generateFieldDeclarations fieldInfos
        
        let fieldInitialisations = this.generateFieldInitialisations fieldInfos
        //updates and bindings: Cover them in an endless loop

        let systemSequence : PrSequence = statementsToSequence (fieldInitialisations)
        let systemProctype = activeProctypeWithNameAndSequence "System" systemSequence
        let systemModule = PrModule.ProcTypeModule(systemProctype)

        {
            PrSpec.Code = [varModule;systemModule];
            PrSpec.Formulas = [];
        }

    member this.transformExpressionInsideAFormula (expression:MMExpression) : PrExpression =
        match expression with
            | MMExpression.BooleanLiteral (value:bool) ->
                match value with
                    | true ->  PrExpression.Const(PrConst.True)
                    | false -> PrExpression.Const(PrConst.False)
            | MMExpression.IntegerLiteral (value:int) ->
                PrExpression.Const(PrConst.Number(value))
            | MMExpression.DecimalLiteral (value:decimal) ->
                failwith "NotImplementedYet"
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformExpressionInsideAFormula operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> PrExpression.UnaryExpr(PrUnarop.Not,transformedOperand)
                    | MMUnaryOperator.Minus      -> PrExpression.UnaryExpr(PrUnarop.Neg,transformedOperand)
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                let transformedLeft = this.transformExpressionInsideAFormula leftExpression
                let transformedRight = this.transformExpressionInsideAFormula rightExpression
                match operator with
                    | MMBinaryOperator.Add                -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Add,transformedRight)
                    | MMBinaryOperator.Subtract           -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Min,transformedRight)
                    | MMBinaryOperator.Multiply           -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Mul,transformedRight)
                    | MMBinaryOperator.Divide             -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Div,transformedRight)
                    | MMBinaryOperator.Modulo             -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Mod,transformedRight)
                    | MMBinaryOperator.LogicalAnd         -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Andor(PrAndor.And),transformedRight)
                    | MMBinaryOperator.LogicalOr          -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Andor(PrAndor.Or),transformedRight)
                    | MMBinaryOperator.Equals             -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Eq,transformedRight)
                    | MMBinaryOperator.NotEquals          -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Neq,transformedRight)
                    | MMBinaryOperator.LessThan           -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Lt,transformedRight)
                    | MMBinaryOperator.LessThanOrEqual    -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Le,transformedRight)
                    | MMBinaryOperator.GreaterThan        -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Gt,transformedRight)
                    | MMBinaryOperator.GreaterThanOrEqual -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Ge,transformedRight)
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    failwith "Use transformExpressionInsideAFormula only for expression inside untransformed formulas and not in components"
                else
                    //called inside a formula
                    let fieldInfo = resolveFieldAccessInsideAFormula componentReference.Value field
                    let varref = this.transformFieldInfoToVarref fieldInfo
                    PrExpression.Varref varref
    (*
    member this.transformExpressionInsideAComponent (comp:MMComponentObject) (expression:MMExpression) : PrExpression =
        match expression with
            | MMExpression.BooleanLiteral (value:bool) ->
                match value with
                    | true ->  PrExpression.Const(PrConst.True)
                    | false -> PrExpression.Const(PrConst.False)
            | MMExpression.IntegerLiteral (value:int) ->
                PrExpression.Const(PrConst.Number(value))
            | MMExpression.DecimalLiteral (value:decimal) ->
                failwith "NotImplementedYet"
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformExpressionInsideAComponent comp operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> PrExpression.UnaryExpr(PrUnarop.Not,transformedOperand)
                    | MMUnaryOperator.Minus      -> PrExpression.UnaryExpr(PrUnarop.Neg,transformedOperand)
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                let transformedLeft = this.transformExpressionInsideAComponent comp leftExpression
                let transformedRight = this.transformExpressionInsideAComponent comp rightExpression
                match operator with
                    | MMBinaryOperator.Add                -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Add,transformedRight)
                    | MMBinaryOperator.Subtract           -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Min,transformedRight)
                    | MMBinaryOperator.Multiply           -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Mul,transformedRight)
                    | MMBinaryOperator.Divide             -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Div,transformedRight)
                    | MMBinaryOperator.Modulo             -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Mod,transformedRight)
                    | MMBinaryOperator.LogicalAnd         -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Andor(PrAndor.And),transformedRight)
                    | MMBinaryOperator.LogicalOr          -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Andor(PrAndor.Or),transformedRight)
                    | MMBinaryOperator.Equals             -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Eq,transformedRight)
                    | MMBinaryOperator.NotEquals          -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Neq,transformedRight)
                    | MMBinaryOperator.LessThan           -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Lt,transformedRight)
                    | MMBinaryOperator.LessThanOrEqual    -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Le,transformedRight)
                    | MMBinaryOperator.GreaterThan        -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Gt,transformedRight)
                    | MMBinaryOperator.GreaterThanOrEqual -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Ge,transformedRight)
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    let fieldInfo = resolveFieldAccessInsideAComponent comp field
                    let varref = this.transformFieldInfoToVarref fieldInfo
                    PrExpression.Varref varref
                else
                    //called inside a formula
                    failwith "Use transformExpressionInsideAComponent only for expression inside components and not in formulas"
    *)           


    member this.transformExpressionInsideASimpleStatement (expression:SimpleExpression) : PrExpression =
        this.transformExpressionInsideAFormula expression
    

    member this.transformSimpleStatement (statement:SimpleStatement) : PrStatement =
        match statement with
            | SimpleStatement.GuardedCommandStatement (optionsOfGuardedCommand:(( SimpleExpression * (SimpleStatement list) ) list)) -> //Context * Guard * Statements  
                let transformOption (guard,sequence) : (SimpleExpression * (SimpleStatement list) ) =
                    let transformedGuard = this.transformExpressionInsideASimpleStatement guard
                    let transformedSequence = sequence |> List.map this.transformSimpleStatement
                    let promelaSequence = statementsToSequence [transformedGuard;transformedSequence]
                    ""
                ""
            | SimpleStatement.AssignmentStatement (target:FieldInfo, ContextOfExpression:Context, Expression:MMExpression) -> //Context is only the Context of the Expression. FieldInfo has its own Context (may result of a return-Statement, when context is different)
                ""
            (*| MMStatement.EmptyStatement ->
                skipStatement
            | MMStatement.BlockStatement (statements : MMStatement list) ->
                statements |> List.map this.transformStatement
                           |> coverInSimpleBlockStatement
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
                failwith "NotImplementedYet"
                (*let transformGuardedStmnt ((guard,stmnt):MMExpression * MMStatement) =
                    let transformedGuard = this.transformExpressionInsideAComponent guard
                    let transformedStmnt = this.transformStatement stmnt
                    PrSequence.Sequence([anyExprToStep transformedGuard;stmntToStep transformedStmnt])
                guardedStmnts |> List.map transformGuardedStmnt
                              |> (fun sequences -> PrStatement.IfStmnt(PrOptions.Options(sequences)))*)
            | MMStatement.AssignmentStatement (target : MMExpression, expression : MMExpression) ->
                failwith "NotImplementedYet"*)

    member this.transformFormula (formula:MMFormula) : PrFormula =
        //TODO: check if LTL
        match formula with
             | MMFormula.StateFormula (stateExpression : MMExpression) ->
                PrFormula.PropositionalStateFormula(this.transformExpressionInsideAFormula stateExpression)
             | MMFormula.UnaryFormula (operand : MMFormula, operator : MMUnaryFormulaOperator) ->
                let transformedOperand = this.transformFormula operand
                match operator with
                    | MMUnaryFormulaOperator.Not      -> PrFormula.UnaryFormula(PrUnaryFormulaOperator.Not,transformedOperand)
                    | MMUnaryFormulaOperator.Next     -> failwith "UnaryTemporalOperator.Next not yet implemented in Promela. There are diverse problems with it. Read http://spinroot.com/spin/Man/ltl.html"
                    | MMUnaryFormulaOperator.Finally  -> PrFormula.UnaryFormula(PrUnaryFormulaOperator.Eventually,transformedOperand)
                    | MMUnaryFormulaOperator.Globally -> PrFormula.UnaryFormula(PrUnaryFormulaOperator.Always,transformedOperand)
                    | _ -> failwith "No CTL available"
             | MMFormula.BinaryFormula (leftFormula : MMFormula, operator : MMBinaryFormulaOperator, rightFormula : MMFormula) ->
                let transformedLeft = this.transformFormula leftFormula
                let transformedRight = this.transformFormula rightFormula
                match operator with
                    | MMBinaryFormulaOperator.And         -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.And,transformedRight)
                    | MMBinaryFormulaOperator.Or          -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Or,transformedRight)
                    | MMBinaryFormulaOperator.Implication -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Implies,transformedRight)
                    | MMBinaryFormulaOperator.Equivalence -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Equals,transformedRight)
                    | MMBinaryFormulaOperator.Until       -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Until,transformedRight)
                    | _ -> failwith "No CTL available"
    
    