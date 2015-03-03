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

namespace SafetySharp.Analysis.VerificationCondition

module internal VcSam =
    // Both the transformation with weakest precondition or strongest postcondition work with a modified Sam-Model.
    
    // every statement also has a statement id = SID
    // TODO: This model also contains a notion of versions for variables.

    // Advantages of this modified Sam-Model:
    //  * Peekhole optimizations are easier.
    //  * Transformation to verification condition is slightly easier.
    // See
    //  * Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions. http://dx.doi.org/10.1145/360204.360220
    //  * Greg Nelson. A generalization of Dijkstra's calculus. http://dx.doi.org/10.1145/69558.69559

    type UOp = SafetySharp.Models.Sam.UOp
    type BOp = SafetySharp.Models.Sam.BOp
    type Var = SafetySharp.Models.Sam.Var
    type Val = SafetySharp.Models.Sam.Val
    type Expr = SafetySharp.Models.Sam.Expr
    
    type StatementId = int option
    
    type Stm =
        | Assert of SID:StatementId * Expression:Expr       //semantics: wp( Stm.Assert(e), phi) := e && phi (formula to prove is false, when assertion is false)
        | Assume of SID:StatementId * Expression:Expr       //semantics: wp( Stm.Assume(e), phi) := e -> phi
        | Block of SID:StatementId * Statements:Stm list
        | Choice of SID:StatementId * Choices:Stm list
        | Write of SID:StatementId * Variable:Var * Expression:Expr
        with
            member this.GetStatementId = function
                | Assert (sid,_) -> sid
                | Assume (sid,_) -> sid
                | Block (sid,_) -> sid
                | Choice (sid,_) -> sid
                | Write (sid,_,_) -> sid
    
    type Type = SafetySharp.Models.Sam.Type
    type GlobalVarDecl = SafetySharp.Models.Sam.GlobalVarDecl
    type LocalVarDecl = SafetySharp.Models.Sam.LocalVarDecl
 
    type Pgm = {
        Globals : GlobalVarDecl list
        Locals : LocalVarDecl list
        Body : Stm
    }

    let rec translateStm (stmIdCounter:int ref) (stm : SafetySharp.Models.Sam.Stm) : Stm =
        do stmIdCounter := stmIdCounter.Value + 1
        let freshId = Some(stmIdCounter.Value)
        match stm with
            | SafetySharp.Models.Sam.Stm.Block(statements) ->
                Stm.Block(freshId,statements |> List.map (translateStm stmIdCounter) )
            | SafetySharp.Models.Sam.Stm.Choice (clauses) ->                
                if clauses = [] then
                    (Stm.Assume(freshId,Expr.Literal(Val.BoolVal(false))))
                else
                    let translateClause ( clause :SafetySharp.Models.Sam.Clause) : Stm =
                        do stmIdCounter := stmIdCounter.Value + 1
                        let freshIdForGuard = Some(stmIdCounter.Value)
                        Stm.Block(freshId,[Stm.Assume(freshIdForGuard,clause.Guard);translateStm stmIdCounter clause.Statement]) // the guard is now an assumption
                    Stm.Choice(freshId,clauses |> List.map translateClause)
            | SafetySharp.Models.Sam.Stm.Write (variable,expression) ->
                Stm.Write (freshId,variable,expression)

    let translatePgm (pgm : SafetySharp.Models.Sam.Pgm ) : Pgm =
        let stmIdCounter = ref (0)
        {
            Pgm.Globals = pgm.Globals;
            Pgm.Locals = pgm.Locals;
            Pgm.Body = translateStm stmIdCounter pgm.Body;
        }
                
    let rec createAndedExpr (exprs:Expr list) : Expr =
        if exprs.IsEmpty then
            Expr.Literal(Val.BoolVal(true)) //see Conjunctive Normal Form. If there is no clause, the formula is true.
        else if exprs.Tail = [] then
            // only one element, so return it
            exprs.Head
        else
            Expr.BExpr(exprs.Head,BOp.And,createAndedExpr exprs.Tail)
                
    let rec createOredExpr (exprs:Expr list) : Expr =
        if exprs.IsEmpty then
            Expr.Literal(Val.BoolVal(false)) //see Conjunctive Normal Form. An empty clause is unsatisfiable.
        else if exprs.Tail = [] then
            // only one element, so return it
            exprs.Head
        else
            Expr.BExpr(exprs.Head,BOp.Or,createOredExpr exprs.Tail)
    
    let unionManyVarMaps<'b when 'b : comparison> (mapsToUnite:Map<Var,'b> list) =
        let rec unionManyVarMaps (united:Map<Var,'b>) (mapsToUnite:Map<Var,'b> list) =
            if mapsToUnite.IsEmpty then
                united
            else
                let newUnited =
                    mapsToUnite.Head |> Map.toList
                                     |> List.fold (fun (united:Map<Var,'b>) (key:Var,value:'b) -> united.Add(key,value)) united
                unionManyVarMaps newUnited mapsToUnite.Tail
        unionManyVarMaps Map.empty<Var,'b> mapsToUnite

module internal VcSamWorkflow =
    open SafetySharp.Workflow
    type VcSamPgm = VcSam.Pgm

    type IVcSamModel<'state> =
        interface
            abstract getModel : VcSam.Pgm
            abstract setModel : VcSam.Pgm -> 'state
        end
           
    let getModel<'state when 'state :> IVcSamModel<'state>> : WorkflowFunction<'state,'state,VcSam.Pgm> = workflow {
        let! state = getState
        let model = state.getModel
        return model
    }    
    
    let setModel<'state when 'state :> IVcSamModel<'state>> (model:VcSam.Pgm) : WorkflowFunction<'state,'state,unit> = workflow {
        let! state = getState
        let newState = state.setModel model
        do! updateState newState
    }

    type PlainVcSamModel(model:VcSam.Pgm) =
        class end
            with
                member this.getModel : VcSam.Pgm = model
                interface IVcSamModel<PlainVcSamModel> with
                    member this.getModel : VcSam.Pgm = model
                    member this.setModel (model:VcSam.Pgm) = PlainVcSamModel(model)
    
    type PlainVCScmModelWorkflowState = WorkflowState<PlainVcSamModel>
    type PlainVCScmModelWorkflowFunction<'returnType> = WorkflowFunction<PlainVcSamModel,PlainVcSamModel,'returnType>

    let createPlainScmWorkFlowState (model:VcSam.Pgm) : PlainVCScmModelWorkflowState =
        WorkflowState<PlainVcSamModel>.stateInit (PlainVcSamModel(model))
    
    let setPlainModelState (model:VcSam.Pgm) = workflow {
        do! updateState (PlainVcSamModel(model))
    }
    
    let toPlainModelState<'state when 'state :> IVcSamModel<'state>> : WorkflowFunction<'state,PlainVcSamModel,unit> = workflow {
        let! state = getState
        do! setPlainModelState state.getModel
    }

    open SafetySharp.Models
    
    type VcExpr = SafetySharp.Models.Sam.Expr

    type SamToVcWorkflowFunction<'stateWithSam> = WorkflowFunction<'stateWithSam,VcExpr,unit>
    
    type SamToVcSamWorkflowFunction<'stateWithSam> = WorkflowFunction<'stateWithSam,PlainVcSamModel,unit>

    type VcSamToVcWorkflowFunction<'stateWithVcSam> = WorkflowFunction<'stateWithVcSam,VcExpr,unit>
        
    let transformSamToVcSam<'stateWithSam when 'stateWithSam :> SamWorkflow.ISamModel<'stateWithSam>> :
                        SamToVcSamWorkflowFunction<'stateWithSam> = workflow {
        let! samModel = SamWorkflow.getModel
        let vcSamModel = VcSam.translatePgm samModel
        do! setPlainModelState vcSamModel
    }

    