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

    let transformValToVal (_val:Scm.Val) : Sam.Val=
        match _val with
            | Scm.BoolVal (_val) -> Sam.BoolVal(_val)
            | Scm.IntVal (_val)  -> Sam.NumbVal(bigint(_val))

    
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

    ////////////////////////////////////////////////

    let transformScmToSam (model : Scm.CompDecl) : Sam.Pgm =
        // first level up and inline everything in Sam, then produce the appropriate Sam.Pgm.
        // The latter is just a recursive walk through the Scm-Datatypes and return the equivalent Sam-Datatypes
        let initialState = initialSimpleState model
        let workFlow = ScmRewriterFlattenModel.levelUpAndInline
        let (_,resultingState) = ScmRewriterBase.runState workFlow initialState
        let newModel = resultingState.Model
        //printf "%s" (SafetySharp.Models.Scm.ScmAstToString.exportModel newModel)

        transformCompDeclToPgm newModel
        