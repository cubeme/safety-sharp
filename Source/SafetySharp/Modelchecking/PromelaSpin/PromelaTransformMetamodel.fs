module PromelaTransformMetamodel

open PromelaAstHelpers

type MMExpression = SafetySharp.Metamodel.Expression
type MMUnaryOperator = SafetySharp.Metamodel.UnaryOperator
type MMBinaryOperator = SafetySharp.Metamodel.BinaryOperator
type MMFieldSymbol = SafetySharp.Metamodel.FieldSymbol
type MMStatement = SafetySharp.Metamodel.Statement
type MMFormula = SafetySharp.Metamodel.Formula

type PrExpression = PromelaDataStructures.Ast.AnyExpr
type PrConst = PromelaDataStructures.Ast.Const
type PrUnarop = PromelaDataStructures.Ast.Unarop
type PrBinarop = PromelaDataStructures.Ast.Binarop
type PrAndor = PromelaDataStructures.Ast.Andor
type PrStatement = PromelaDataStructures.Ast.Stmnt
type PrOptions = PromelaDataStructures.Ast.Options
type PrSequence = PromelaDataStructures.Ast.Sequence
type PrStep = PromelaDataStructures.Ast.Step


type MetamodelToPromela() =

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

    member this.transformFormula (formula:MMFormula) : =
    //TODO Write Operator