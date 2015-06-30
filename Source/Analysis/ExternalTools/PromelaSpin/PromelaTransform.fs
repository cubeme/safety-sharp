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

// TODO: CHECK EVERY CYCLE, IF RANGES ARE RESPECTED!!!!!!

// IDEA: 
//   - Use pool of temporary fields of each type for the implementation of temporary variables
//       * Determine the size of the pool
//   - If a field isn't used later on, set it to its initial value to keep state space small
//       * for this introduce a set "lastUsage". Associate the lastUsage to the stmnt, if it is used in
//         the statement or expression itself. When traversing the list of statements here add a map field->field of pool
//         and put the field back to the pool it isn't used in the future
//   - Remove temporary fields from state vector (if possible)


module internal SamToPromela =
    open SafetySharp.EngineOptions
    open TsamHelpers

    let forceExprToBeInRangeOfVar = SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.forceExprToBeInRangeOfVar

    let promelaGlobalVarJustInitialized = "globalVarJustInitialized"

    let generateGlobalVarDeclarations (varDecls:Sam.GlobalVarDecl list) : PrOneDecl list =
        let generateDecl (varDecl:Sam.GlobalVarDecl) : PrOneDecl =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> PrTypename.Bool
                            | Sam.Type.IntType -> PrTypename.Int
                            //| Sam.Type.Decimal -> failwith "NotImplementedYet"
                            | Sam.Type.RangedIntType _ -> PrTypename.Int
                            | Sam.Type.RealType -> failwith "No support in Promela for real values, yet."
                            | Sam.Type.RangedRealType _ -> failwith "No support in Promela for real values, yet."
            let _varName = varDecl.Var.getName 
            let _variable = PrIvar.Ivar(_varName,None,None)
            PrOneDecl.OneDecl(None,_type,[_variable])
        let varDeclsFromSam = varDecls |> List.map generateDecl
        let promelaGlobalVarJustInitializedDecl = PrOneDecl.OneDecl(None,PrTypename.Bool,[PrIvar.Ivar(promelaGlobalVarJustInitialized,None,None)])
        varDeclsFromSam @ [promelaGlobalVarJustInitializedDecl]
                 
                 
    let generateLocalVarDeclarations (varDecls:Sam.LocalVarDecl list) : PrOneDecl list =
        let generateDecl (varDecl:Sam.LocalVarDecl) : PrOneDecl =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> PrTypename.Bool
                            | Sam.Type.IntType -> PrTypename.Int
                            //| Sam.Type.Decimal -> failwith "NotImplementedYet"
                            | Sam.Type.RangedIntType _ -> PrTypename.Int
                            | Sam.Type.RealType -> failwith "No support in Promela for real values, yet."
                            | Sam.Type.RangedRealType _ -> failwith "No support in Promela for real values, yet."
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
            | Sam.Val.RealVal _ -> failwith "No support in Promela for real values, yet."
            | Sam.Val.ProbVal _ -> failwith "No support in Promela for probabilities, yet."

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
        

    let generateResetLocalVarsStatements (varDecls:Sam.LocalVarDecl list) : PrStatement list =
        let generateResetStatement (varDecl:Sam.LocalVarDecl) : PrStatement =
            let assignVarref = transformSamVarToVarref varDecl.Var
            let assignExpr = transformSamVal (varDecl.Type.getDefaultValue)
            PrStatement.AssignStmnt(PrAssign.AssignExpr(assignVarref,assignExpr))
        varDecls |> List.map generateResetStatement
                                                
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
            | Sam.Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                let guardExpr = transformSamExpr guardExpr
                let thenExpr = transformSamExpr thenExpr
                let elseExpr = transformSamExpr elseExpr
                PrExpression.IfThenElse(guardExpr,thenExpr,elseExpr)
            | Sam.Expr.ReadOld (variable) ->
                failwith "NotImplementedYet"
                
    let generateRangeGlobalVarsStatements (semanticsOfAssignmentToRangedVariables:TsamEngineOptions.SemanticsOfAssignmentToRangedVariables)
                                          (varToType:Map<Sam.Var,Sam.Type>)
                                          (varDecls:Sam.GlobalVarDecl list)
                                : PrStatement list =        
        match semanticsOfAssignmentToRangedVariables with
            | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep ->
                let forceVariableToBeInRange (varDecl:Sam.GlobalVarDecl) : PrStatement =
                    let assignVarref = transformSamVarToVarref varDecl.Var  
                    let expr = Sam.Expr.Read(varDecl.Var)
                    let newExpr = forceExprToBeInRangeOfVar varToType varDecl.Var expr
                    let assignExpr = transformSamExpr newExpr
                    PrStatement.AssignStmnt(PrAssign.AssignExpr(assignVarref,assignExpr))
                varDecls |> List.map forceVariableToBeInRange
            | _ ->
                []
        
    let generateAssertInvariantStatements (invariants:Sam.Expr list) : PrStatement list =
        let generateAssertInvariantStatement (invariant:Sam.Expr) : PrStatement =
            let invariant = transformSamExpr invariant
            PrStatement.AssertStmnt(Expr.AnyExpr invariant)
        invariants |> List.map generateAssertInvariantStatement

    let rec transformSamStm (semanticsOfAssignmentToRangedVariables:TsamEngineOptions.SemanticsOfAssignmentToRangedVariables)
                            (varToType:Map<Sam.Var,Sam.Type>)
                            (statement:Sam.Stm)
                    : PrStatement =                          
        let applyAssignmentSemanticsAfterAssignment (expr:Sam.Expr) (_var:Sam.Var) =
            match semanticsOfAssignmentToRangedVariables with
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangeAfterEveryAssignmentToAGlobalVar ->
                    forceExprToBeInRangeOfVar varToType _var expr
                | _ ->
                    expr

        match statement with
            | Sam.Stm.Block (statements:Sam.Stm list) ->
                if statements.IsEmpty then
                    PrStatement.ExprStmnt(Expr.AnyExpr(AnyExpr.Const(Const.Skip)))
                else
                    statements |> List.map (transformSamStm semanticsOfAssignmentToRangedVariables varToType)
                               |> List.map (fun stm -> Step.StmntStep(stm,None))
                               |> PrSequence.Sequence
                               |> PrStatement.SequenceStmnt
            | Sam.Stm.Choice (clauses:Sam.Clause list) ->
                let transformOption (clause : Sam.Clause) =
                    let transformedGuard = transformSamExpr clause.Guard
                    let transformedGuardStmnt = anyExprToStmnt transformedGuard
                    let transformedStm = transformSamStm semanticsOfAssignmentToRangedVariables varToType clause.Statement
                    let promelaSequence = statementsToSequence [transformedGuardStmnt;transformedStm]
                    promelaSequence
                clauses |> List.map transformOption
                        |> PrOptions.Options
                        |> PrStatement.IfStmnt

            | Sam.Stm.Write (variable:Sam.Var, expression:Sam.Expr) ->
                let expressionInRange = applyAssignmentSemanticsAfterAssignment expression variable
                let transformedTarget = transformSamVarToVarref variable
                let transformedExpression = transformSamExpr expressionInRange
                createAssignmentStatement transformedTarget transformedExpression
            | Sam.Stm.Stochastic _ ->
                // Very faint idea:
                //   Via embedded C code it might be possible to calculate the probability of each branch. This might be printed out
                //   for a branch.
                //      float probability = 1.0f
                //      probability *= prob * probability
                //   see http://spinroot.com/spin/Man/float.html
                failwith "Promela does not support stochastic statements"
                
                
    let transformConfiguration (semanticsOfAssignmentToRangedVariables:TsamEngineOptions.SemanticsOfAssignmentToRangedVariables)
                               (invariants:Sam.Expr list)
                               (pgm:Sam.Pgm)
                        : (PrSpec*Map<Sam.Traceable,string>) = // returns new program * forward tracing map
        // remove unwanted chars and assure, that no unwanted characters are in the string
        let changeIdsState = ChangeIdentifierState.initial Set.empty<string> SafetySharp.FreshNameGenerator.namegenerator_c_like
        let (pgm,forwardTrace) = changeNamesPgm changeIdsState pgm
        
        let varToType =
            let varToTypeWithGlobals = pgm.Globals |> List.fold (fun (acc:Map<Sam.Var,Sam.Type>) elem -> acc.Add(elem.Var,elem.Type)) (Map.empty<Sam.Var,Sam.Type>)
            let varToTypeWithGlobalsAndLocals = pgm.Locals |> List.fold (fun (acc:Map<Sam.Var,Sam.Type>) elem -> acc.Add(elem.Var,elem.Type)) (varToTypeWithGlobals)
            varToTypeWithGlobalsAndLocals

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
                
        let rangeGlobalVars = generateRangeGlobalVarsStatements semanticsOfAssignmentToRangedVariables varToType pgm.Globals
        
        let resetLocalVars = generateResetLocalVarsStatements pgm.Locals

        let assertInvariants = generateAssertInvariantStatements invariants

        // initialize globals
        let globalVarInitialisations =
            // cover initialization in atomic block. Example, why this is necessary.
            // If we have a formula "[] A==B" and the initialization ensures this property (by setting A to 1 and B to 1),
            // in a short moment, A is 1 and B is still 0. Atomic block ensures, that A and B are set in the same point of time.
            let globalVarsInitializations =  (generateGlobalVarInitialisations pgm.Globals)
            let initializations = globalVarsInitializations @ resetLocalVars
            if initializations.IsEmpty then
                []
            else 
                [coverInAtomicBlockStatement (initializations)]    

        let globalVarsJustInitializedToTrue =
            // For the ltl-formula (drafted in the ltlTransformation) to work we need to set
            // promelaGlobalVarJustInitialized to false after the first loop
            // Otherwise the patch of "[] A==B+1" would not work. The patch is "F (globalVarInitialized && ([] A==B+1))". It might otherwise be
            // valid even if the "[] ..." is only true beginning from the 20th step.
            PrStatement.AssignStmnt(PrAssign.AssignExpr(PrVarref.Varref(promelaGlobalVarJustInitialized,None,None),PrExpression.Const(PrConst.True)))
        let globalVarsJustInitializedToFalse =
            PrStatement.AssignStmnt(PrAssign.AssignExpr(PrVarref.Varref(promelaGlobalVarJustInitialized,None,None),PrExpression.Const(PrConst.False)))

        let codeOfMetamodelInAtomicLoop =
            let stmWithoutNestedBlocks = pgm.Body.simplifyBlocks
            let codeOfMetamodel = transformSamStm semanticsOfAssignmentToRangedVariables varToType stmWithoutNestedBlocks
            [coverStmInEndlessloop (coverInAtomicBlockStatement (assertInvariants @ [codeOfMetamodel]@resetLocalVars@rangeGlobalVars @ [globalVarsJustInitializedToFalse]))]
        
        let systemModule =
            let systemCode = globalVarInitialisations @ [globalVarsJustInitializedToTrue] @ codeOfMetamodelInAtomicLoop
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
    open SafetySharp.ITracing

    type PromelaTracer<'traceableOfOrigin> = {
        PrSpec : PrSpec;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> PrTraceable;
    }
        with
            interface ITracing<PrSpec,'traceableOfOrigin,PrTraceable,PromelaTracer<'traceableOfOrigin>> with
                member this.getModel = this.PrSpec
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> PrTraceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> PrTraceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables = []
    
    let transformConfigurationWithInvariantsWf<'traceableOfOrigin> (invariants:Sam.Expr list) : ExogenousWorkflowFunction<SamTracer.SamTracer<'traceableOfOrigin>,PromelaTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()        
        let! semanticsOfAssignmentToRangedVariables =            
            getEngineOption<_,TsamEngineOptions.SemanticsOfAssignmentToRangedVariables> ()   
            
        // We cannot execute the tsam-transformation for explicit assignments here directly. TODO: After unifying SAM and TSAM do it and replace code
        // assert (state.Pgm.Attributes.SemanticsOfAssignmentToRangedVariablesAppliedExplicitly = SafetySharp.Ternary.True)

        let isSemanticsOptionDoable =
            match semanticsOfAssignmentToRangedVariables with
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangeAfterEveryAssignmentToAGlobalVar
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.IgnoreRanges
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep ->
                    true
                | _ ->
                    false
        assert (isSemanticsOptionDoable)

        let samModel = state.Pgm
        let (newPromelaSpec,forwardTraceInClosure) = transformConfiguration semanticsOfAssignmentToRangedVariables invariants samModel
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            forwardTraceInClosure.Item beforeTransform
        let transformed =
            {
                PromelaTracer.PrSpec = newPromelaSpec;
                PromelaTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                PromelaTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }
    let transformConfigurationWf<'traceableOfOrigin> () : ExogenousWorkflowFunction<SamTracer.SamTracer<'traceableOfOrigin>,PromelaTracer<'traceableOfOrigin>> =
        transformConfigurationWithInvariantsWf<'traceableOfOrigin> []

    
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
            | Scm.Val.RealVal _ -> failwith "No support in Promela for real values, yet."
            | Scm.Val.ProbVal _ -> failwith "No support in Promela for probabilities, yet."
                                            
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

        
    // TODO: Actually we need to add the variable "globalVarInitialized" to the ltl-formula.
    // Otherwise "[] A==B+1" would not work. "F (globalVarInitialized && ([] A==B+1))".
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
                                
module internal ScmToPromela =

    open SafetySharp.Workflow
    open SafetySharp.Models.ScmTracer
    open SafetySharp.Analysis.VerificationCondition
                

    let transformConfigurationWithInvariants<'state when 'state :> IScmTracer<Scm.Traceable,'state>> (invariants:ScmVerificationElements.PropositionalExpr list)
                        : ExogenousWorkflowFunction<'state,SamToPromela.PromelaTracer<Scm.Traceable>> = workflow {
        // TODO: After backmerging Tsam into Sam this hack is not necessary anymore! We could get rid of this transformation. Assertions could just be prepended to a loop
        
        
        do! SafetySharp.Models.ScmToSam.transformIscmToSam
        let! state = getState ()
        let samInvariants = invariants |> List.map (ScmVeToSam.transformScmVePropositionalExprToSamExpr state.ForwardTracer)
        do! SamToPromela.transformConfigurationWithInvariantsWf (samInvariants)
    }
               
    let transformConfiguration<'traceableOfOrigin,'state when 'state :> IScmTracer<'traceableOfOrigin,'state>> ()
                        : ExogenousWorkflowFunction<'state,SamToPromela.PromelaTracer<'traceableOfOrigin>> = workflow {        
        do! SafetySharp.Models.ScmToSam.transformIscmToSam
        do! SamToPromela.transformConfigurationWf ()
    }
