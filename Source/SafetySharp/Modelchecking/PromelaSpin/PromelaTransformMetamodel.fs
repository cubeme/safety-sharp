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
type MMSubcomponentSymbol = SafetySharp.Metamodel.ComponentReferenceSymbol
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

type Context = {
    partition : MMPartitionObject;
    container : MMComponentObject list; //last object is root; head is a subComponent of its parent:  subComponent1(::parentOfSubComponent1)*::rootComponent. Construction is done in "collectFields"
}

type FieldInfo = {
    context : Context;
    field : MMFieldObject; //TODO: maybe switch to MMFieldSymbol. Cannot find any advantage of using MMFieldObject yet
}

// many steps are a sequence
type MMStepInfo = {
    context : Context;
    statement : MMStatement;
}

// An easyStatement has only assignments and guarded commands. Also Assignments are defined on fieldinfos
type EasyStatement = 
    | GuardedCommandStatement of (Context * MMExpression * (EasyStatement list) ) list //Context * Guard * Statements
    | AssignmentStatement of Target : FieldInfo * Context : Context * Expression : MMExpression //Context is only the Context of the Expression. FieldInfo has its own Context (may result of a return-Statement, when context is different)
       
type MetamodelToPromela() =
    let getSubComponentObjects (subcomponentMap : Map<MMSubcomponentSymbol, MMComponentObject>) : (MMComponentObject list) =
        subcomponentMap |> Map.fold (fun acc key value -> value::acc) []
    
    let getFieldObjects (fieldMap : Map<MMFieldSymbol, MMFieldObject>) : (MMFieldObject list) =
        fieldMap |> Map.fold (fun acc key value -> value::acc) []


    let collectFields (model : MMModelObject) : FieldInfo list =
        let rec collectFromComponent (partition:MMPartitionObject) (parents:MMComponentObject list) (comp:MMComponentObject) : FieldInfo list = 
            let collectedInSubcomponents : FieldInfo list=
                (getSubComponentObjects comp.Subcomponents) |> List.collect (fun comp -> collectFromComponent partition (comp::parents) comp)
            let collectFieldInThisComponent (fieldobject:MMFieldObject) =
                {
                    FieldInfo.context = {
                                            Context.partition = partition;
                                            Context.container = comp::parents;
                                        }
                    FieldInfo.field = fieldobject;
                }
            let collectedInThisComponent = (getFieldObjects comp.Fields) |> List.map collectFieldInThisComponent 
            collectedInThisComponent @ collectedInSubcomponents
        let collectFromPartition (partition:MMPartitionObject) : FieldInfo list  =
            collectFromComponent partition [] partition.RootComponent
        model.Partitions |> List.collect collectFromPartition
    
    let rec resolveFieldInfo (context:Context) (expression:MMExpression) : FieldInfo = 
        match expression with
            | MMExpression.BooleanLiteral (value:bool) ->
                failwith "target of assignment cannot be a constant value"
            | MMExpression.IntegerLiteral (value:int) ->
                failwith "target of assignment cannot be a constant value"
            | MMExpression.DecimalLiteral (value:decimal) ->
                failwith "target of assignment cannot be a constant value"
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                (*let transformedOperand = this.transformExpression operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> PrExpression.UnaryExpr(PrUnarop.Not,transformedOperand)
                    | MMUnaryOperator.Minus      -> PrExpression.UnaryExpr(PrUnarop.Neg,transformedOperand)
                *)
                failwith "NotImplementedYet"
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                (*let transformedLeft = this.transformExpression leftExpression
                let transformedRight = this.transformExpression rightExpression
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
                *)
                failwith "NotImplementedYet"
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol) ->
                {
                    FieldInfo.context=context;
                    FieldInfo.field = (context.container.Head.Fields.Item field);
                }
        

    let rec transformMMStepInfosToEasyStatements (methodBodyResolver:MMMethodBodyResolver) (collected:EasyStatement list) (toTransform:MMStepInfo list) : EasyStatement list =
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
                    transformMMStepInfosToEasyStatements methodBodyResolver collected newToTransform
                | MMStatement.BlockStatement (statements : MMStatement list) ->
                    let coverStatementWithContext (statement:MMStatement) =
                        {
                            MMStepInfo.context=contextOfStatement;
                            MMStepInfo.statement=statement;
                        }
                    let expandedBlockStatement = statements |> List.map coverStatementWithContext
                    let newToTransform = expandedBlockStatement @ toTransform.Tail
                    transformMMStepInfosToEasyStatements methodBodyResolver collected newToTransform
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
                    failwith "NotImplementedYet"
            
    // build (toTransform:MMStepInfo list) with all updates in the correct order
    // let collectPartitionUpdateSequence =
    //      TODO
    //   - Only updates, no bindings
    //   - TODO: Updates are proccessed in the correct order

    member this.transformFieldInfoToName (fieldInfo : FieldInfo) =
        let partitionName = "pA" //partition has no name, use A as dummy. TODO: find something better
        let componentName =
            fieldInfo.context.container |> List.map (fun comp -> comp.Name)
                                        |> List.rev //the order should be root::subcomponent::leafSubcomponent
                                        |> List.fold (fun acc elem -> acc + "_c" + elem) ""
        let fieldName = "_f"+fieldInfo.field.FieldSymbol.Name
        sprintf "%s%s%s" partitionName componentName fieldName

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
        let fields = collectFields configuration.ModelObject
        
        let varModule = this.generateFieldDeclarations fields
        
        let fieldInitialisations = this.generateFieldInitialisations fields
        //updates and bindings: Cover them in an endless loop

        let systemSequence : PrSequence = statementsToSequence (fieldInitialisations)
        let systemProctype = activeProctypeWithNameAndSequence "System" systemSequence
        let systemModule = PrModule.ProcTypeModule(systemProctype)

        {
            PrSpec.Code = [varModule;systemModule];
            PrSpec.Formulas = [];
        }

    

    member this.transformExpression (expression:MMExpression) : PrExpression =
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
                let transformedOperand = this.transformExpression operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> PrExpression.UnaryExpr(PrUnarop.Not,transformedOperand)
                    | MMUnaryOperator.Minus      -> PrExpression.UnaryExpr(PrUnarop.Neg,transformedOperand)
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                let transformedLeft = this.transformExpression leftExpression
                let transformedRight = this.transformExpression rightExpression
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
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, componentReference) ->
                failwith "NotImplementedYet"

    member this.transformStatement (statement:MMStatement) : PrStatement =
        match statement with
            | MMStatement.EmptyStatement ->
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
                let transformGuardedStmnt ((guard,stmnt):MMExpression * MMStatement) =
                    let transformedGuard = this.transformExpression guard
                    let transformedStmnt = this.transformStatement stmnt
                    PrSequence.Sequence([anyExprToStep transformedGuard;stmntToStep transformedStmnt])
                guardedStmnts |> List.map transformGuardedStmnt
                              |> (fun sequences -> PrStatement.IfStmnt(PrOptions.Options(sequences)))
            | MMStatement.AssignmentStatement (target : MMExpression, expression : MMExpression) ->
                failwith "NotImplementedYet"

    member this.transformFormula (formula:MMFormula) : PrFormula =
        //TODO: check if LTL
        match formula with
             | MMFormula.StateFormula (stateExpression : MMExpression) ->
                PrFormula.PropositionalStateFormula(this.transformExpression stateExpression)
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
    
    