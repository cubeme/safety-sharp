// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Analysis.Modelchecking.PromelaSpin

open PromelaAstHelpers
open SafetySharp.Analysis.Modelchecking
open SafetySharp.Analysis.Modelchecking.PromelaSpin.Typedefs
open SafetySharp.Models
open SafetySharp.Models.SamHelpers
open SafetySharp.Models.SamChangeIdentifier
open SafetySharp.Models.SamSimplifyBlocks

// IDEA: 
//   - Use pool of temporary fields of each type for the implementation of temporary variables
//       * Determine the size of the pool
//   - If a field isn't used later on, set it to its initial value to keep state space small
//       * for this introduce a set "lastUsage". Associate the lastUsage to the stmnt, if it is used in
//         the statement or expression itself. When traversing the list of statements here add a map field->field of pool
//         and put the field back to the pool it isn't used in the future
//   - Remove temporary fields from state vector (if possible)


module internal SamToPromela =
    let generateGlobalVarDeclarations (varDecls:Sam.GlobalVarDecl list) : PrOneDecl list =
        let generateDecl (varDecl:Sam.GlobalVarDecl) : PrOneDecl =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> PrTypename.Bool
                            | Sam.Type.IntType -> PrTypename.Int
                            //| Sam.Type.Decimal -> failwith "NotImplementedYet"
            let _varName = varDecl.Var.getName 
            let _variable = PrIvar.Ivar(_varName,None,None)
            PrOneDecl.OneDecl(None,_type,[_variable])
        varDecls |> List.map generateDecl
                 
                 
    let generateLocalVarDeclarations (varDecls:Sam.LocalVarDecl list) : PrOneDecl list =
        let generateDecl (varDecl:Sam.LocalVarDecl) : PrOneDecl =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> PrTypename.Bool
                            | Sam.Type.IntType -> PrTypename.Int
                            //| Sam.Type.Decimal -> failwith "NotImplementedYet"
            let _varName = varDecl.Var.getName 
            let _variable = PrIvar.Ivar(_varName,None,None)
            PrOneDecl.OneDecl(None,_type,[_variable])
        varDecls |> List.map generateDecl
                 
    let transformSamVarToVarref ( var:Sam.Var ) =
        let varName = var.getName
        PrVarref.Varref(varName,None,None)

    let transformSamVal (literal:Sam.Val) : PrExpression =
        match literal with
            | Sam.Val.NumbVal (value) ->
                    PrExpression.Const(PrConst.Number(  int32(value) ))
            | Sam.Val.BoolVal (value) ->
                match value with
                    | true  -> PrExpression.Const(PrConst.True)
                    | false -> PrExpression.Const(PrConst.False)

    let generateGlobalVarInitialisations (varDecls:Sam.GlobalVarDecl list) : PrStatement list =
        let generateInit (varDecl:Sam.GlobalVarDecl) : PrStatement =
            let generateSequence (initialValue : Sam.Val) : PrSequence =
                let assignVarref = transformSamVarToVarref varDecl.Var
                let assignExpr = transformSamVal initialValue
                //also possible to add a "true" as a guard to the returned sequence
                statementsToSequence [PrStatement.AssignStmnt(PrAssign.AssignExpr(assignVarref,assignExpr))]                
            varDecl.Init |> List.map generateSequence
                         |> PrOptions.Options
                         |> PrStatement.IfStmnt
        varDecls |> List.map generateInit


                                
    let rec transformSamExpr (expression:Sam.Expr) : PrExpression =
        match expression with
            | Sam.Expr.Literal (value:Sam.Val) ->
                transformSamVal value
            | Sam.Expr.UExpr (operand, operator) ->
                let transformedOperand = transformSamExpr operand
                match operator with
                    | Sam.UOp.Not -> PrExpression.UnaryExpr(PrUnarop.Not,transformedOperand)
                    //| Sam.UOp.      -> PrExpression.UnaryExpr(PrUnarop.Neg,transformedOperand)
            | Sam.Expr.BExpr (leftExpression,operator,rightExpression) ->
                let transformedLeft = transformSamExpr leftExpression
                let transformedRight = transformSamExpr rightExpression
                match operator with
                    | Sam.BOp.Add         -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Add,transformedRight)
                    | Sam.BOp.Subtract    -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Min,transformedRight)
                    | Sam.BOp.Multiply    -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Mul,transformedRight)
                    | Sam.BOp.Divide      -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Div,transformedRight)
                    | Sam.BOp.Modulo      -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Mod,transformedRight)
                    | Sam.BOp.And         -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Andor(PrAndor.And),transformedRight)
                    | Sam.BOp.Or          -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Andor(PrAndor.Or),transformedRight)
                    | Sam.BOp.Implies     -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Le,transformedRight) // true -> false := 1 <= 0
                    | Sam.BOp.Equals      -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Eq,transformedRight)
                    | Sam.BOp.NotEquals   -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Neq,transformedRight)
                    | Sam.BOp.Less        -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Lt,transformedRight)
                    | Sam.BOp.LessEqual   -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Le,transformedRight)
                    | Sam.BOp.Greater     -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Gt,transformedRight)
                    | Sam.BOp.GreaterEqual -> PrExpression.BinaryExpr(transformedLeft,PrBinarop.Ge,transformedRight)
            | Sam.Expr.Read (variable) ->
                let varref = transformSamVarToVarref variable
                PrExpression.Varref varref
            | Sam.Expr.ReadOld (variable) ->
                failwith "NotImplementedYet"

        
    let rec transformSamStm (statement:Sam.Stm) : PrStatement =
        match statement with
            | Sam.Stm.Block (statements:Sam.Stm list) ->
                if statements.IsEmpty then
                    PrStatement.ExprStmnt(Expr.AnyExpr(AnyExpr.Const(Const.Skip)))
                else
                    statements |> List.map transformSamStm
                               |> List.map (fun stm -> Step.StmntStep(stm,None))
                               |> PrSequence.Sequence
                               |> PrStatement.SequenceStmnt
            | Sam.Stm.Choice (clauses:Sam.Clause list) ->
                let transformOption (clause : Sam.Clause) =
                    let transformedGuard = transformSamExpr clause.Guard
                    let transformedGuardStmnt = anyExprToStmnt transformedGuard
                    let transformedStm = transformSamStm clause.Statement
                    let promelaSequence = statementsToSequence [transformedGuardStmnt;transformedStm]
                    promelaSequence
                clauses |> List.map transformOption
                        |> PrOptions.Options
                        |> PrStatement.IfStmnt

            | Sam.Stm.Write (variable:Sam.Var, expression:Sam.Expr) ->
                let transformedTarget = transformSamVarToVarref variable
                let transformedExpression = transformSamExpr expression
                createAssignmentStatement transformedTarget transformedExpression            
                
                
    let transformConfiguration (pgm:Sam.Pgm) : (PrSpec*Map<Sam.Traceable,string>) = // returns new program * forward tracing map
        // remove unwanted chars and assure, that no unwanted characters are in the string
        let changeIdsState = ChangeIdentifierState.initial Set.empty<string> SafetySharp.FreshNameGenerator.namegenerator_c_like
        let (pgm,forwardTrace) = changeNamesPgm changeIdsState pgm
        
        let forwardTrace = forwardTrace |> Map.toList |> List.map (fun (samVar,promelaVar) -> (Sam.Traceable(samVar),promelaVar.getName) ) |> Map.ofList

        // declare both locals and globals
        let globalVarModule = generateGlobalVarDeclarations pgm.Globals
        let localVarModule = generateLocalVarDeclarations pgm.Locals
        let varModule =
            if globalVarModule.IsEmpty && localVarModule.IsEmpty then
                // A DeclList in Promela needs at least one member
                []
            else
                [(globalVarModule@localVarModule) |> PrDeclLst.DeclLst |> PrModule.GlobalVarsAndChans]


        // initialize globals
        let globalVarInitialisations = generateGlobalVarInitialisations pgm.Globals
        

        let codeOfMetamodelInLoop =
            let stmWithoutNestedBlocks = pgm.Body.simplifyBlocks
            let codeOfMetamodel = transformSamStm stmWithoutNestedBlocks
            [coverStmInEndlessloop codeOfMetamodel]
        
        let systemModule =
            let systemCode = globalVarInitialisations @ codeOfMetamodelInLoop
            let systemSequence : PrSequence = statementsToSequence (globalVarInitialisations @ codeOfMetamodelInLoop)
            let systemProctype = activeProctypeWithNameAndSequence "System" systemSequence
            [PrModule.ProcTypeModule(systemProctype)]
        let newPromelaSpec =
            {
                PrSpec.Code = varModule @ systemModule;
                PrSpec.Formulas = [];
            }
        (newPromelaSpec,forwardTrace)
    

    open SafetySharp.Workflow
    
    let transformConfigurationWf<'traceableOfOrigin> () : ExogenousWorkflowFunction<Sam.Pgm,PrSpec,'traceableOfOrigin,Sam.Traceable,string,unit> = workflow {
        let! samModel = SamWorkflow.getSamModel ()
        let (newPromelaSpec,forwardTraceInClosure) = transformConfiguration samModel
        do! updateState newPromelaSpec
        
        let intermediateTracer (oldValue:Sam.Traceable) = forwardTraceInClosure.Item oldValue
        do! updateTracer intermediateTracer
    }

    
module internal ScmToPromela =

    open SafetySharp.Workflow
    open SafetySharp.Models.ScmWorkflow
    open SafetySharp.Analysis.VerificationCondition
                
    let transformConfiguration<'traceableOfOrigin,'state when 'state :> IScmModel<'state>> ()
                        : ExogenousWorkflowFunction<'state,PrSpec,'traceableOfOrigin,Scm.Traceable,string,unit> = workflow {
        do! SafetySharp.Models.ScmToSam.transformIscmToSam
        do! SamToPromela.transformConfigurationWf ()
    }

    (*

    

    // TODO: maybe an alternative is to transform a formula to a SimpleFormula
    let transformExpressionInsideAFormula (expression:MMExpression) : PrExpression =
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
            | MMExpression.ReadField (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    failwith "Use transformExpressionInsideAFormula only for expression inside untransformed formulas and not in components"
                else
                    //called inside a formula
                    let simpleGlobalField = toSimplifiedMetamodel.resolveFieldAccessInsideAFormula componentReference.Value field
                    let varref = this.transformSamVarToVarref simpleGlobalField
                    PrExpression.Varref varref
            | MMExpression.ReadLocal (local:MMLocalSymbol) ->
                failwith "NotImplementedYet"
            | MMExpression.ReadParameter (parameter:MMParameterSymbol) ->
                failwith "NotImplementedYet"
          
            


    let transformFormula (formula:MMFormula) : PrFormula =
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
    
    *)