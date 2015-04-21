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
            | Sam.Stm.Stochastic _ ->
                // Very faint idea:
                //   Via embedded C code it might be possible to calculate the probability of each branch. This might be printed out
                //   for a branch.
                //      float probability = 1.0f
                //      probability *= prob * probability
                //   see http://spinroot.com/spin/Man/float.html
                failwith "Promela does not support stochastic statements"
                
                
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
        let globalVarInitialisations =
            // cover initialization in atomic block. Example, why this is necessary.
            // If we have a formula "[] A==B" and the initialization ensures this property (by setting A to 1 and B to 1),
            // in a short moment, A is 1 and B is still 0. Atomic block ensures, that A and B are set in the same point of time.
            let initializations =  (generateGlobalVarInitialisations pgm.Globals)
            if initializations.IsEmpty then
                []
            else 
                [coverInAtomicBlockStatement (generateGlobalVarInitialisations pgm.Globals)]
        

        let codeOfMetamodelInAtomicLoop =
            let stmWithoutNestedBlocks = pgm.Body.simplifyBlocks
            let codeOfMetamodel = transformSamStm stmWithoutNestedBlocks
            [coverStmInEndlessloop (coverInAtomicBlockStatement [codeOfMetamodel])]
        
        let systemModule =
            let systemCode = globalVarInitialisations @  codeOfMetamodelInAtomicLoop
            let systemSequence : PrSequence = statementsToSequence (systemCode)
            let systemProctype = activeProctypeWithNameAndSequence "System" systemSequence
            [PrModule.ProcTypeModule(systemProctype)]
        let newPromelaSpec =
            {
                PrSpec.Code = varModule @ systemModule;
                PrSpec.Formulas = [];
            }
        (newPromelaSpec,forwardTrace)
    

    open SafetySharp.Workflow
    
    let transformConfigurationWf<'traceableOfOrigin> () : ExogenousWorkflowFunction<Sam.Pgm,PrSpec,'traceableOfOrigin,Sam.Traceable,PrTraceable,unit> = workflow {
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
                        : ExogenousWorkflowFunction<'state,PrSpec,'traceableOfOrigin,Scm.Traceable,PrTraceable,unit> = workflow {
        do! SafetySharp.Models.ScmToSam.transformIscmToSam
        do! SamToPromela.transformConfigurationWf ()
    }

module internal ScmVeToPromela =
    
    open ScmVerificationElements
        
    let transformScmVal (literal:Scm.Val) : PrLtlExpr =
        match literal with
            | Scm.Val.IntVal (value) ->
                    PrLtlExpr.Const(PrConst.Number(  value ))
            | Scm.Val.BoolVal (value) ->
                match value with
                    | true  -> PrLtlExpr.Const(PrConst.True)
                    | false -> PrLtlExpr.Const(PrConst.False)
                                            
    let transformBinaryOperator (operator:Scm.BOp) =
        match operator with
            | Scm.BOp.Add          -> PrBinarop.Add
            | Scm.BOp.Subtract     -> PrBinarop.Min
            | Scm.BOp.Multiply     -> PrBinarop.Mul
            | Scm.BOp.Divide       -> PrBinarop.Div
            | Scm.BOp.Modulo       -> PrBinarop.Mod
            | Scm.BOp.And          -> PrBinarop.Andor(PrAndor.And)
            | Scm.BOp.Or           -> PrBinarop.Andor(PrAndor.Or)
            | Scm.BOp.Equals       -> PrBinarop.Eq
            | Scm.BOp.NotEquals    -> PrBinarop.Neq
            | Scm.BOp.Less         -> PrBinarop.Lt
            | Scm.BOp.LessEqual    -> PrBinarop.Le
            | Scm.BOp.Greater      -> PrBinarop.Gt
            | Scm.BOp.GreaterEqual -> PrBinarop.Ge

    let transformUnaryOperator (operator:Scm.UOp) =
        match operator with
            | Scm.UOp.Not -> PrUnarop.Not
            | Scm.UOp.Minus -> failwith "NotImplementedYet"
                
    let transformBinaryLtlOperator (operator:LbOp) =
        match operator with
            | LbOp.Until -> BinaryLtlOperator.Until

    let transformUnaryLtlOperator (operator:LuOp) =
        match operator with
            | LuOp.Next -> 
                failwith "Spin is not particularly suited to check next formulas. Read http://spinroot.com/spin/Man/ltl.html"
            | LuOp.Globally -> UnaryLtlOperator.Always
            | LuOp.Eventually -> UnaryLtlOperator.Eventually


    let transformScmFieldToVarref (tracer:Scm.Traceable->string) (compPath:Scm.CompPath,field:Scm.Field) : PrVarref =
        let varName = tracer (Scm.TraceableField(compPath,field))
        PrVarref.Varref(varName,None,None)

    let transformScmFaultToVarref (tracer:Scm.Traceable->string) (compPath:Scm.CompPath,fault:Scm.Fault) : PrVarref =
        let varName = tracer (Scm.TraceableFault(compPath,fault))
        PrVarref.Varref(varName,None,None)

    let rec transformLtlExpression (tracer:Scm.Traceable->string) (expression:LtlExpr) : PrLtlExpr =
        match expression with
            | LtlExpr.Literal  (value) ->
                transformScmVal value
            | LtlExpr.ReadField (compPath,field) ->
                PrLtlExpr.Varref ( transformScmFieldToVarref tracer (compPath,field))
            | LtlExpr.ReadFault (compPath,fault) ->
                PrLtlExpr.Varref ( transformScmFaultToVarref tracer (compPath,fault))
            | LtlExpr.UExpr (expr,op) ->
                let transformedOperator = transformUnaryOperator op
                let transformedOperand = (transformLtlExpression tracer) expr
                PrLtlExpr.UnaryExpr(transformedOperator,transformedOperand)
            | LtlExpr.BExpr  (left,op,right) ->
                let transformedLeft = (transformLtlExpression tracer) left
                let transformedRight = (transformLtlExpression tracer) right
                let transformedOperator = transformBinaryOperator op
                PrLtlExpr.BinaryExpr(transformedLeft,transformedOperator,transformedRight)
            | LtlExpr.LuExpr (expr,op) ->
                let transformedOperator = transformUnaryLtlOperator op
                let transformedOperand = (transformLtlExpression tracer) expr
                PrLtlExpr.UnaryLtlExpr(transformedOperand,transformedOperator)
            | LtlExpr.LbExpr (left,op,right) ->
                let transformedLeft = (transformLtlExpression tracer) left
                let transformedRight = (transformLtlExpression tracer) right
                let transformedOperator = transformBinaryLtlOperator op
                PrLtlExpr.BinaryLtlExpr(transformedLeft,transformedOperator,transformedRight)

