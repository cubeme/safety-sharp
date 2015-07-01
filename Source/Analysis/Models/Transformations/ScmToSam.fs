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

namespace SafetySharp.Models

open SafetySharp.Models
open SafetySharp.Models.ScmRewriterBase
open SafetySharp.Models.ScmRewriterFlattenModel

type ScmFault = SafetySharp.Models.Scm.Fault
type ScmFaultExpr = SafetySharp.Models.Scm.FaultExpr

module internal ScmToSam =

    let transformVarToVar (var:Scm.Var) : Sam.Var =
        match var with
            | Scm.Var (name) -> Sam.Var(name)
            
    let transformFieldToVar (field:Scm.Field) : Sam.Var =
        match field with
            | Scm.Field (name) -> Sam.Var(name)

    let transformTypeToType (_type:Scm.Type) : Sam.Type =
        match _type with
            | Scm.BoolType -> Sam.BoolType
            | Scm.IntType -> Sam.IntType
            | Scm.RealType -> Sam.RealType
            | Scm.RangedIntType(_from,_to,_overflow) -> Sam.RangedIntType(_from,_to,_overflow)
            | Scm.RangedRealType(_from,_to,_overflow) -> Sam.RangedRealType(_from,_to,_overflow)

    let transformValToVal (_val:Scm.Val) : Sam.Val=
        match _val with
            | Scm.BoolVal (_val) -> Sam.BoolVal(_val)
            | Scm.IntVal (_val)  -> Sam.NumbVal(bigint(_val))
            | Scm.RealVal (_val)  -> Sam.RealVal(_val)
            | Scm.ProbVal (_val)  -> Sam.ProbVal(_val)

    
    let transformUopToUop (uop:Scm.UOp) : Sam.UOp =
        match uop with
            //| Scm.Minus -> Sam.Min
            | Scm.Not   -> Sam.Not
            | _ -> failwith "No Minus here (yet?)"

    let transformBopToBop (bop:Scm.BOp) : Sam.BOp=
        match bop with
            | Scm.Add          -> Sam.Add
            | Scm.Subtract     -> Sam.Subtract
            | Scm.Multiply     -> Sam.Multiply
            | Scm.Divide       -> Sam.Divide
            | Scm.Modulo       -> Sam.Modulo
            | Scm.And          -> Sam.And
            | Scm.Or           -> Sam.Or
            | Scm.Equals       -> Sam.Equals
            | Scm.NotEquals    -> Sam.NotEquals
            | Scm.Less         -> Sam.Less
            | Scm.LessEqual    -> Sam.LessEqual
            | Scm.Greater      -> Sam.Greater
            | Scm.GreaterEqual -> Sam.GreaterEqual
            
    let transformFieldToGlobalVar (field:Scm.FieldDecl) : Sam.GlobalVarDecl =
        {
            Sam.GlobalVarDecl.Type = transformTypeToType field.Type;
            Sam.GlobalVarDecl.Var = transformFieldToVar field.Field;
            Sam.GlobalVarDecl.Init = field.Init |> List.map transformValToVal;
        }

    let transFormLocalVarToLocalVar (var:Scm.VarDecl) : Sam.LocalVarDecl =
        {
            Sam.LocalVarDecl.Type = transformTypeToType var.Type;
            Sam.LocalVarDecl.Var = transformVarToVar var.Var;
        }
        
    let rec transformExprToExpr (expr:Scm.Expr) : Sam.Expr =
        match expr with            
            | Scm.Literal (_val) -> Sam.Expr.Literal (transformValToVal _val)
            | Scm.ReadVar (_var) -> Sam.Expr.Read(transformVarToVar _var)
            | Scm.ReadField (field) -> Sam.Expr.Read(transformFieldToVar field)
            | Scm.UExpr (expr, uop) ->
                let operator = transformUopToUop uop
                let operand = transformExprToExpr expr
                Sam.UExpr(operand,operator)
            | Scm.BExpr (leftExpr,bop,rightExpr) ->
                let leftExpr = transformExprToExpr leftExpr
                let bop = transformBopToBop bop
                let rightExpr = transformExprToExpr rightExpr
                Sam.BExpr(leftExpr,bop,rightExpr)

    let rec transformStmToStm (stm:Scm.Stm) : Sam.Stm =
        match stm with
            | Scm.AssignVar (var, expr) ->
                let var = transformVarToVar var
                let expr = transformExprToExpr expr
                Sam.Write(var,expr)
            | Scm.AssignField (field, expr) ->
                let var = transformFieldToVar field
                let expr = transformExprToExpr expr
                Sam.Write(var,expr)
            | Scm.AssignFault (_) -> failwith "Statements are expected not to assign to a fault. By inlining with levelUpAndInline you can convert the model to a new model with this property!"
            | Scm.Block (stms) -> 
                let newStmnts = stms |> List.map transformStmToStm
                Sam.Stm.Block(newStmnts)
            | Scm.Choice (choices:(Scm.Expr * Scm.Stm) list) ->
                let transformChoice (expr,stm) =
                    {
                        Sam.Clause.Guard = transformExprToExpr expr;
                        Sam.Clause.Statement = transformStmToStm stm;
                    }
                let newChoices = choices |> List.map transformChoice
                Sam.Stm.Choice(newChoices)
            | Scm.Stochastic (choices:(Scm.Expr * Scm.Stm) list) ->
                let transformChoice (expr,stm) =
                    (transformExprToExpr expr,transformStmToStm stm)
                let newChoices = choices |> List.map transformChoice
                Sam.Stm.Stochastic(newChoices)
            | Scm.CallPort (_) -> failwith "Statements are expected not to call a port. By inlining with levelUpAndInline you can convert the model to a new model with this property!"
            | Scm.StepComp  (_) -> failwith "Statements are expected not to perform a component step. By inlining with levelUpAndInline you can convert the model to a new model with this property!"
            | Scm.StepFault  (_) -> failwith "Statements are expected not to perform a fault step. By inlining with levelUpAndInline you can convert the model to a new model with this property!"

    let transformCompDeclToPgm (model:Scm.CompDecl) : Sam.Pgm =
        let globalVars = model.Fields |> List.map transformFieldToGlobalVar
        if model.Steps.Length <> 1 then
            failwith "Model is expected to have exactly one step. By inlining with levelUpAndInline you can convert the model to a new model with this property!"
        let localVars = model.Steps.Head.Behavior.Locals |> List.map transFormLocalVarToLocalVar
        let stm = model.Steps.Head.Behavior.Body |> transformStmToStm
        {
            Sam.Pgm.Globals = globalVars;
            Sam.Pgm.Locals = localVars;
            Sam.Pgm.Body = stm;
        }

    let createForwardTracingMap (scmModel:Scm.CompDecl) (samModel:Sam.Pgm): Map<Scm.Traceable,Sam.Traceable> =
        // assume fields are in the same order as global vars
        let toTraceable (field:Scm.FieldDecl,gl:Sam.GlobalVarDecl) =
            let scmTraceable =
                Scm.TraceableField( [scmModel.Comp] , field.Field)
            let samTraceable =
                Sam.Traceable(gl.Var)
            (scmTraceable,samTraceable)        
        List.zip (scmModel.Fields) (samModel.Globals)
            |> List.map toTraceable
            |> Map.ofList

    ////////////////////////////////////////////////
            
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmTracer
    open SafetySharp.Models.ScmHelpers

    let transformIscmToSam<'traceableOfOrigin,'oldState when 'oldState :> IScmTracer<'traceableOfOrigin,'oldState>>
                        : ExogenousWorkflowFunction<'oldState,SamTracer.SamTracer<'traceableOfOrigin>> = workflow {
        do! ScmRewriterFlattenModel.flattenModel ()
        do! iscmCommitForwardTracerMap ()
        let! state = getState ()

        let oldModel = state.Model
        let newModel = transformCompDeclToPgm (oldModel.getRootComp)

        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            let mapInClosure = createForwardTracingMap oldModel.getRootComp newModel
            let intermediateTracer (oldValue:Scm.Traceable) =
                match oldValue with
                    | Scm.Traceable.TraceableRemoved(reason) -> Sam.TraceableRemoved(reason)
                    | _ -> mapInClosure.Item oldValue
            intermediateTracer beforeTransform
        let transformed =
            {
                SamTracer.SamTracer.Pgm = newModel
                SamTracer.SamTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                SamTracer.SamTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }

module internal ScmVeToSam =
    open ScmVerificationElements
    
    let rec transformScmVePropositionalExprToSamExpr (forwardTracer:Scm.Traceable-> Sam.Traceable) (expr:PropositionalExpr) : Sam.Expr =
        match expr with            
            | PropositionalExpr.Literal (_val) ->
                Sam.Expr.Literal (ScmToSam.transformValToVal _val)
            | PropositionalExpr.ReadFault (faultComp,fault) ->
                let traced = forwardTracer (Scm.Traceable.TraceableFault(faultComp,fault))
                match traced with
                    | Sam.Traceable(_var) -> Sam.Expr.Read(_var)
                    | Sam.TraceableRemoved (reason) -> failwith ("variable you talk about was removed because " + reason)
            | PropositionalExpr.ReadField (fieldComp,field) ->
                let traced = forwardTracer (Scm.Traceable.TraceableField(fieldComp,field))
                match traced with
                    | Sam.Traceable(_var) -> Sam.Expr.Read(_var)
                    | Sam.TraceableRemoved (reason) -> failwith ("variable you talk about was removed because " + reason)
            | PropositionalExpr.UExpr (expr, uop) ->
                let operator = ScmToSam.transformUopToUop uop
                let operand = transformScmVePropositionalExprToSamExpr forwardTracer expr
                Sam.UExpr(operand,operator)
            | PropositionalExpr.BExpr (leftExpr,bop,rightExpr) ->
                let leftExpr = transformScmVePropositionalExprToSamExpr forwardTracer leftExpr
                let bop = ScmToSam.transformBopToBop bop
                let rightExpr = transformScmVePropositionalExprToSamExpr forwardTracer rightExpr
                Sam.BExpr(leftExpr,bop,rightExpr)