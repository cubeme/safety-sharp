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
open SafetySharp.Modelchecking

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

           
type MetamodelToPromela (configuration:MMConfiguration)  =
    let toSimplifiedMetamodel = MetamodelToSimplifiedMetamodel(configuration)


    // To transform the metamodel to Promela, we take an intermediate step:
    //   metamodel -> simplified metamodel -> promela code
    
    // THIS IS THE MAIN FUNCTION AND ENTRY POINT
    member this.transformConfiguration  : PrSpec =
        let varModule = this.generateFieldDeclarations
        
        let fieldInitialisations = this.generateFieldInitialisations
        
        //updates and bindings: Cover them in an endless loop
        let partitionStatements =
            //TODO: Correct semantics with bindings and correct "interleaving" of bindings and partitions
            configuration.ModelObject.Partitions |> List.collect this.generatePartitionUpdateCode 
        let codeOfMetamodel = partitionStatements
            
        let systemSequence : PrSequence = statementsToSequence (fieldInitialisations @ codeOfMetamodel)
        let systemProctype = activeProctypeWithNameAndSequence "System" systemSequence
        let systemModule = PrModule.ProcTypeModule(systemProctype)

        {
            PrSpec.Code = [varModule;systemModule];
            PrSpec.Formulas = [];
        }


    member this.transformSimpleGlobalFieldToName (simpleGlobalField : SimpleGlobalField) =
        // this is something model checker specific, as different model checkers may have different constraints for identifier
        let partitionName = "p" + simpleGlobalField.context.rootComponentName + "_"
        let hierarchicalAccessName =
            simpleGlobalField.context.hierarchicalAccess |> List.rev //the order should be root::subcomponent::leafSubcomponent
                                                 |> List.map (fun elem -> "c"+elem) //add c in front of every element
                                                 |> String.concat "_"
        let fieldName = "_f"+simpleGlobalField.field.FieldSymbol.Name
        sprintf "%s%s%s" partitionName hierarchicalAccessName fieldName

    member this.transformSimpleGlobalFieldToVarref (simpleGlobalField : SimpleGlobalField) =
        let varName = this.transformSimpleGlobalFieldToName simpleGlobalField
        PrVarref.Varref(varName,None,None)
    
    member this.generateFieldDeclarations : PrModule =
        let fields = toSimplifiedMetamodel.getSimpleGlobalFields
        let generateDecl (field:SimpleGlobalField) : PrOneDecl =
            let _type = match field.field.FieldSymbol.Type with
                            | MMTypeSymbol.Boolean -> PrTypename.Bool
                            | MMTypeSymbol.Integer -> PrTypename.Int
                            | MMTypeSymbol.Decimal -> failwith "NotImplementedYet"
            let _varName = this.transformSimpleGlobalFieldToName field
            let _variable = PrIvar.Ivar(_varName,None,None)
            PrOneDecl.OneDecl(None,_type,[_variable])
        fields |> List.map generateDecl
               |> PrDeclLst.DeclLst
               |> PrModule.GlobalVarsAndChans

    member this.generateFieldInitialisations : PrStatement list =
        let fields = toSimplifiedMetamodel.getSimpleGlobalFields
        let generateInit (field:SimpleGlobalField) : PrStatement =
            let generateSequence (initialValue : obj) : PrSequence =
                let assignVarref = this.transformSimpleGlobalFieldToVarref field
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
    

    member this.generatePartitionUpdateCode (partition:MMPartitionObject) : PrStatement list=
        let partitionUpdateInSimpleStatements = toSimplifiedMetamodel.partitionUpdateInSimpleStatements partition
        let transformedSimpleStatements = partitionUpdateInSimpleStatements |> List.map this.transformSimpleStatement
        transformedSimpleStatements

    // This is currently a TODO
    member this.generatePartitionBindingCode =
        ""
    


    // TODO: maybe an alternative is to transform a formula to a SimpleFormula
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
                    let simpleGlobalField = toSimplifiedMetamodel.resolveFieldAccessInsideAFormula componentReference.Value field
                    let varref = this.transformSimpleGlobalFieldToVarref simpleGlobalField
                    PrExpression.Varref varref
                    
    member this.transformSimpleExpression (expression:SimpleExpression) : PrExpression =
        match expression with
            | SimpleExpression.BooleanLiteral (value:bool) ->
                match value with
                    | true ->  PrExpression.Const(PrConst.True)
                    | false -> PrExpression.Const(PrConst.False)
            | SimpleExpression.IntegerLiteral (value:int) ->
                PrExpression.Const(PrConst.Number(value))
            | SimpleExpression.DecimalLiteral (value:decimal) ->
                failwith "NotImplementedYet"
            | SimpleExpression.UnaryExpression (operand:SimpleExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformSimpleExpression operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> PrExpression.UnaryExpr(PrUnarop.Not,transformedOperand)
                    | MMUnaryOperator.Minus      -> PrExpression.UnaryExpr(PrUnarop.Neg,transformedOperand)
            | SimpleExpression.BinaryExpression (leftExpression:SimpleExpression, operator:MMBinaryOperator, rightExpression : SimpleExpression) ->
                let transformedLeft = this.transformSimpleExpression leftExpression
                let transformedRight = this.transformSimpleExpression rightExpression
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
            | SimpleExpression.FieldAccessExpression (field:SimpleGlobalField) ->
                let varref = this.transformSimpleGlobalFieldToVarref field
                PrExpression.Varref varref
            

    member this.transformSimpleStatement (statement:SimpleStatement) : PrStatement =
        match statement with
            | SimpleStatement.GuardedCommandStatement (optionsOfGuardedCommand:(( SimpleExpression * (SimpleStatement list) ) list)) -> //Context * Guard * Statements  
                let transformOption ((guard,sequence) : (SimpleExpression * (SimpleStatement list) )) =
                    let transformedGuard = this.transformSimpleExpression guard
                    let transformedGuardStmnt = anyExprToStmnt transformedGuard
                    let transformedSequence = sequence |> List.map this.transformSimpleStatement
                    let promelaSequence = statementsToSequence (transformedGuardStmnt::transformedSequence)
                    promelaSequence
                optionsOfGuardedCommand |> List.map transformOption
                                        |> PrOptions.Options
                                        |> PrStatement.IfStmnt
            | SimpleStatement.AssignmentStatement (target:SimpleGlobalField, expression:SimpleExpression) -> //Context is only the Context of the Expression. SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)
                let transformedTarget = this.transformSimpleGlobalFieldToVarref target
                let transformedExpression = this.transformSimpleExpression expression
                createAssignmentStatement transformedTarget transformedExpression

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
    
    