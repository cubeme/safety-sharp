module PromelaTransformMetamodel

open PromelaAstHelpers

type MMModelObject = SafetySharp.Metamodel.ModelObject
type MMPartitionObject = SafetySharp.Metamodel.PartitionObject
type MMComponentObject = SafetySharp.Metamodel.ComponentObject
type MMFieldObject = SafetySharp.Metamodel.FieldObject

type MMTypeSymbol = SafetySharp.Metamodel.TypeSymbol
type MMFieldSymbol = SafetySharp.Metamodel.FieldSymbol
type MMParameterSymbol = SafetySharp.Metamodel.ParameterSymbol
type MMMethodSymbol = SafetySharp.Metamodel.MethodSymbol
type MMSubcomponentSymbol = SafetySharp.Metamodel.SubcomponentSymbol
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

type PrExpression = PromelaDataStructures.Ast.AnyExpr
type PrConst = PromelaDataStructures.Ast.Const
type PrUnarop = PromelaDataStructures.Ast.Unarop
type PrBinarop = PromelaDataStructures.Ast.Binarop
type PrAndor = PromelaDataStructures.Ast.Andor
type PrStatement = PromelaDataStructures.Ast.Stmnt
type PrOptions = PromelaDataStructures.Ast.Options
type PrSequence = PromelaDataStructures.Ast.Sequence
type PrStep = PromelaDataStructures.Ast.Step
type PrFormula = PromelaDataStructures.Ast.Formula
type PrBinaryFormulaOperator = PromelaDataStructures.Ast.BinaryFormulaOperator
type PrUnaryFormulaOperator = PromelaDataStructures.Ast.UnaryFormulaOperator
type PrVarref = PromelaDataStructures.Ast.Varref
type PrProctype = PromelaDataStructures.Ast.Proctype
type PrDeclLst = PromelaDataStructures.Ast.DeclLst
type PrModule = PromelaDataStructures.Ast.Module
type PrOneDecl = PromelaDataStructures.Ast.OneDecl
type PrTypename = PromelaDataStructures.Ast.Typename
type PrIvar = PromelaDataStructures.Ast.Ivar
type PrAssign = PromelaDataStructures.Ast.Assign


type FieldInfo = {
    partition : MMPartitionObject
    container : MMComponentObject list;
    field : MMFieldObject;
}

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
                FieldInfo.partition = partition;
                FieldInfo.container = comp::parents;
                FieldInfo.field = fieldobject;
            }
        let collectedInThisComponent = (getFieldObjects comp.Fields) |> List.map collectFieldInThisComponent 
        collectedInThisComponent @ collectedInSubcomponents
    let collectFromPartition (partition:MMPartitionObject) : FieldInfo list  =
        collectFromComponent partition [] partition.RootComponent
    model.Partitions |> List.collect collectFromPartition
        
type MetamodelToPromela() =    
    member this.transformFieldInfoToName (fieldInfo : FieldInfo) =
        let partitionName = "pA" //partition has no name, use A as dummy. TODO: find something better
        let componentName =
            fieldInfo.container |> List.map (fun comp -> comp.Name)
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
                let assignmentStep =
                    PrStep.StmntStep(PrStatement.AssignStmnt(PrAssign.AssignExpr(assignVarref,assignExpr)),None)
                PrSequence.Sequence([assignmentStep])
            field.field.InitialValues |> List.map generateSequence
                                      |> PrOptions.Options
                                      |> PrStatement.IfStmnt
        fields |> List.map generateInit
        

    member this.generatePartitionUpdateCode =
        []

    member this.generatePartitionBindingCode =
        ""

    member this.transformModelObject (model:MMModelObject) : PrProctype =
        ""


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
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol) ->
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
    
    