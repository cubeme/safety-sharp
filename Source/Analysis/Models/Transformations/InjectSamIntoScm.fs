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

open ScmHelpers

module internal InjectSamIntoScm =
    
    let transformSamTypeToScmType (_type:Sam.Type) : Scm.Type =
        match _type with
            | Sam.BoolType -> Scm.BoolType
            | Sam.IntType -> Scm.IntType
            | Sam.RealType -> Scm.RealType
            | Sam.RangedIntType(_from,_to,_overflow) -> Scm.RangedIntType(_from,_to,_overflow)
            | Sam.RangedRealType(_from,_to,_overflow) -> Scm.RangedRealType(_from,_to,_overflow)

    let transformSamValToScmVal (_val:Sam.Val) : Scm.Val=
        match _val with
            | Sam.BoolVal (_val) -> Scm.BoolVal(_val)
            | Sam.NumbVal (_val)  -> Scm.IntVal(int _val)
            | Sam.RealVal (_val)  -> Scm.RealVal(_val)
            | Sam.ProbVal (_val)  -> Scm.ProbVal(_val)

    
    let transformSamUopToScmUop (uop:Sam.UOp) : Scm.UOp =
        match uop with
            | Sam.Not   -> Scm.Not

    let transformSamBopToScmBop (bop:Sam.BOp) : Scm.BOp=
        match bop with
            | Sam.Add          -> Scm.Add
            | Sam.Subtract     -> Scm.Subtract
            | Sam.Multiply     -> Scm.Multiply
            | Sam.Divide       -> Scm.Divide
            | Sam.Modulo       -> Scm.Modulo
            | Sam.And          -> Scm.And
            | Sam.Or           -> Scm.Or
            | Sam.Equals       -> Scm.Equal
            | Sam.NotEquals    -> Scm.NotEqual
            | Sam.Less         -> Scm.Less
            | Sam.LessEqual    -> Scm.LessEqual
            | Sam.Greater      -> Scm.Greater
            | Sam.GreaterEqual -> Scm.GreaterEqual
            | _                -> failwith "NotSupportedYet"
         
    let rec transformSamExprToScmExpr (globalVarsToFields:Map<Sam.Var,Scm.Field>,localVarsToLocal:Map<Sam.Var,Scm.Var>) (expr:Sam.Expr) : Scm.Expr =
        let transform = transformSamExprToScmExpr (globalVarsToFields,localVarsToLocal)
        match expr with
            | Sam.Expr.Literal (_val) ->
                Scm.Expr.Literal (transformSamValToScmVal _val)
            | Sam.Expr.Read (_var) ->
                if (globalVarsToFields.ContainsKey _var) then
                    Scm.Expr.ReadField( globalVarsToFields.Item _var)
                else
                    Scm.Expr.ReadVar(localVarsToLocal.Item _var)
            | Sam.Expr.ReadOld (_var) ->
                failwith "NotSupportedYet"
            | Sam.Expr.UExpr (expr,uop) ->
                Scm.Expr.UExpr( transform expr, transformSamUopToScmUop uop)
            | Sam.Expr.BExpr (exprLeft, bop, exprRight) ->
                Scm.Expr.BExpr(transform exprLeft,transformSamBopToScmBop bop,transform exprRight)
            | Sam.Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                failwith "NotSupportedYet"

    let rec transformSamStmToScmStm (globalVarsToFields:Map<Sam.Var,Scm.Field>,localVarsToLocal:Map<Sam.Var,Scm.Var>) (stm:Sam.Stm) : Scm.Stm =
        let transformStm = transformSamStmToScmStm (globalVarsToFields,localVarsToLocal)
        let transformExpr = transformSamExprToScmExpr (globalVarsToFields,localVarsToLocal)
        match stm with
            | Sam.Stm.Block (stmts) ->
                Scm.Stm.Block(stmts |> List.map transformStm)
            | Sam.Stm.Choice (choices:Sam.Clause list) ->
                let transformChoice (choice:Sam.Clause) = (transformExpr choice.Guard,transformStm choice.Statement)
                Scm.Stm.Choice(choices |> List.map transformChoice)
            | Sam.Stm.Stochastic (stochasticChoices) ->
                let transformChoice (probability,stm) = (transformExpr probability,transformStm stm)
                Scm.Stm.Stochastic(stochasticChoices |> List.map transformChoice)        
            | Sam.Stm.Write (_var,expr) ->
                let expr = transformExpr expr
                if (globalVarsToFields.ContainsKey _var) then
                    Scm.Stm.AssignField( globalVarsToFields.Item _var,expr)
                else
                    Scm.Stm.AssignVar( localVarsToLocal.Item _var,expr)
            
    let transformSamGlobalVarToScmField (globalVarsToFields:Map<Sam.Var,Scm.Field>) (globalVar:Sam.GlobalVarDecl) : Scm.FieldDecl =
        {
            Scm.FieldDecl.Type = transformSamTypeToScmType globalVar.Type;
            Scm.FieldDecl.Field = globalVarsToFields.Item globalVar.Var;
            Scm.FieldDecl.Init = globalVar.Init |> List.map transformSamValToScmVal;
        }

    let transformSamLocalVarToScmLocalVar (localVarsToLocal:Map<Sam.Var,Scm.Var>) (var:Sam.LocalVarDecl) : Scm.VarDecl =
        {
            Scm.VarDecl.Type = transformSamTypeToScmType var.Type;
            Scm.VarDecl.Var = localVarsToLocal.Item var.Var;
        }       
    let transformSamPgmToScmCompDecl (name:Scm.Comp) (pgm:Sam.Pgm) : (Scm.CompDecl) =
        let globalVarsToFields = pgm.Globals |> List.map (fun gl -> match gl.Var with | Sam.Var(varName)-> (gl.Var,Scm.Field(varName) )) |> Map.ofList
        let localVarsToLocal = pgm.Locals |> List.map (fun l -> match l.Var with | Sam.Var(varName)-> (l.Var,Scm.Var(varName) )) |> Map.ofList
        let stepBehavior =
            {
                Scm.BehaviorDecl.Locals = pgm.Locals |> List.map (transformSamLocalVarToScmLocalVar localVarsToLocal);
                Scm.BehaviorDecl.Body = transformSamStmToScmStm (globalVarsToFields,localVarsToLocal) pgm.Body
            }
        let step =
            {
                Scm.StepDecl.Contract = Scm.Contract.None;
                Scm.StepDecl.FaultExpr = None;
                Scm.StepDecl.Behavior = stepBehavior;
            }
        {
            Scm.CompDecl.Comp = name;
            Scm.CompDecl.Subs = [];
            Scm.CompDecl.Fields = pgm.Globals |> List.map (transformSamGlobalVarToScmField globalVarsToFields);
            Scm.CompDecl.Faults = [];
            Scm.CompDecl.ReqPorts = [];
            Scm.CompDecl.ProvPorts = [];
            Scm.CompDecl.Bindings = [];
            Scm.CompDecl.Steps = [step];
        }

    let injectSam (injectIntoModel:Scm.ScmModel) (modelToInject:Sam.Pgm) (injectIntoPath:Scm.CompPath) : Scm.ScmModel =
        let componentToReplace = injectIntoPath.Head
        let transformedSam = transformSamPgmToScmCompDecl componentToReplace modelToInject
        let newRootComponent = injectIntoModel.getRootComp.replaceDescendant injectIntoPath transformedSam
        Scm.ScmModel(newRootComponent)
        
    ////////////////////////////////////////////////
            
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmTracer
    open SafetySharp.Models.ScmHelpers

    let injectSamWorkflow (samModel:Sam.Pgm) (path:Scm.CompPath) : EndogenousWorkflowFunction<Scm.ScmModel> = workflow {
        let! injectIntoModel = getState ()
        let newModel = injectSam injectIntoModel samModel path
        do! updateState newModel
    }
