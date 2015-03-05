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
            member this.GetStatementId : StatementId =
                match this with
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

    let mergeEntriesOfVarSetMap<'b when 'b : comparison> (oldEntries:Map<Var,Set<'b>>) (newEntries:Map<Var,Set<'b>>) : Map<Var,Set<'b>> =
        let newEntries = newEntries |> Map.toSeq
        let mergeVariables (state:Map<Var,Set<'b>>) (_var:Var,newEntries:Set<'b>) : Map<Var,Set<'b>> =
            if not(state.ContainsKey _var) then
                state.Add(_var,newEntries)
            else
                let oldEntries = oldEntries.Item _var
                let mergedEntries = Set.union oldEntries newEntries
                state.Add(_var,mergedEntries)
        Seq.fold mergeVariables oldEntries newEntries
        

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

    
    type VcExpr = SafetySharp.Models.Sam.Expr
    type SamToVcWorkflowFunction<'stateWithSam> = WorkflowFunction<'stateWithSam,VcExpr,unit>



    // VcSam: PlainModel
    type PlainModel(model:VcSam.Pgm) =
        class end
            with
                member this.getModel : VcSam.Pgm = model
                interface IVcSamModel<PlainModel> with
                    member this.getModel : VcSam.Pgm = model
                    member this.setModel (model:VcSam.Pgm) = PlainModel(model)
    
    type PlainModelWorkflowState = WorkflowState<PlainModel>
    type PlainModelWorkflowFunction<'returnType> = WorkflowFunction<PlainModel,PlainModel,'returnType>

    let createPlainModelWorkFlowState (model:VcSam.Pgm) : PlainModelWorkflowState =
        WorkflowState<PlainModel>.stateInit (PlainModel(model))
    
    let setPlainModelState (model:VcSam.Pgm) = workflow {
        do! updateState (PlainModel(model))
    }
    
    let toPlainModelState<'state when 'state :> IVcSamModel<'state>> : WorkflowFunction<'state,PlainModel,unit> = workflow {
        let! state = getState
        do! setPlainModelState state.getModel
    }
    

module internal VcSamModelForModification =
    open SafetySharp.Workflow
    open VcSamWorkflow

    let rec translateStm (stmIdCounter:int ref) (stm : SafetySharp.Models.Sam.Stm) : VcSam.Stm =
        do stmIdCounter := stmIdCounter.Value + 1
        let freshId = Some(stmIdCounter.Value)
        match stm with
            | SafetySharp.Models.Sam.Stm.Block(statements) ->
                VcSam.Stm.Block(freshId,statements |> List.map (translateStm stmIdCounter) )
            | SafetySharp.Models.Sam.Stm.Choice (clauses) ->                
                if clauses = [] then
                    (VcSam.Stm.Assume(freshId,VcSam.Expr.Literal(VcSam.Val.BoolVal(false))))
                else
                    let translateClause ( clause :SafetySharp.Models.Sam.Clause) : VcSam.Stm =
                        do stmIdCounter := stmIdCounter.Value + 1
                        let freshIdForGuard = Some(stmIdCounter.Value)
                        VcSam.Stm.Block(freshId,[VcSam.Stm.Assume(freshIdForGuard,clause.Guard);translateStm stmIdCounter clause.Statement]) // the guard is now an assumption
                    VcSam.Stm.Choice(freshId,clauses |> List.map translateClause)
            | SafetySharp.Models.Sam.Stm.Write (variable,expression) ->
                VcSam.Stm.Write (freshId,variable,expression)
                
    let translatePgm (stmIdCounter:int ref) (pgm : SafetySharp.Models.Sam.Pgm ) : VcSam.Pgm =
        {
            VcSam.Pgm.Globals = pgm.Globals;
            VcSam.Pgm.Locals = pgm.Locals;
            VcSam.Pgm.Body = translateStm stmIdCounter pgm.Body;
        }
        
    let rec getMaximalStmId (stm:VcSam.Stm) : int =
        match stm with
            | VcSam.Stm.Assert (sid,_) ->
                sid.Value
            | VcSam.Stm.Assume (sid,_) ->
                sid.Value
            | VcSam.Stm.Block (sid,statements) ->
                statements |> List.map getMaximalStmId
                           |> List.max
            | VcSam.Stm.Choice (sid,choices) ->
                choices |> List.map getMaximalStmId
                        |> List.max
            | VcSam.Stm.Write (sid,_,_) ->
                sid.Value

    // VcSam: Model with generator for fresh versions of variables
    type ModelForModification =
        {
            StmIdCounter : int ref;
            Model : VcSam.Pgm;
        }
            with
                static member initial (model:SafetySharp.Models.Sam.Pgm) =
                    let counter = ref 0
                    {
                        ModelForModification.StmIdCounter = counter;
                        ModelForModification.Model = translatePgm counter model;
                    }                    
                static member initial (model:VcSam.Pgm) =
                    let counter = ref (getMaximalStmId model.Body)
                    {
                        ModelForModification.StmIdCounter = counter;
                        ModelForModification.Model = model;
                    }
                member this.getFreshId (): int =
                    do this.StmIdCounter:=this.StmIdCounter.Value + 1
                    this.StmIdCounter.Value

                interface IVcSamModel<ModelForModification> with
                    member this.getModel : VcSam.Pgm = this.Model
                    member this.setModel (model:VcSam.Pgm) =
                        { this with
                            ModelForModification.Model = model;
                        }
    
    type ModelForModificationWorkflowState = WorkflowState<ModelForModification>
    type ModelForModificationWorkflowFunction<'returnType> = WorkflowFunction<ModelForModification,ModelForModification,'returnType>

    let setModelForModificationState (model:VcSam.Pgm) = workflow {
        let! oldState = getModel
        do! setModel model
    }
    
    
    open SafetySharp.Models
    type SamToVcSamWorkflowFunction<'stateWithSam> = WorkflowFunction<'stateWithSam,ModelForModification,unit>
    type VcSamToVcWorkflowFunction<'stateWithVcSam> = WorkflowFunction<'stateWithVcSam,VcExpr,unit>
        
    let transformSamToVcSam<'stateWithSam when 'stateWithSam :> SamWorkflow.ISamModel<'stateWithSam>> :
                        SamToVcSamWorkflowFunction<'stateWithSam> = workflow {
        let! model = SafetySharp.Models.SamWorkflow.getModel
        let newModel = (ModelForModification.initial model)
        do! updateState newModel
    }

    let transformIVcSamToVcModelForModification<'state when 'state :> IVcSamModel<'state>>
                     : WorkflowFunction<'state,ModelForModification,unit> = workflow {
        let! model = getModel
        let newModel = (ModelForModification.initial model)
        do! updateState newModel
    }