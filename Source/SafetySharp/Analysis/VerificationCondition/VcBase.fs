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
    
    type Stm =
        | Assert of Expression : Expr       //semantics: wp( Stm.Assert(e), phi) := e && phi (formula to prove is false, when assertion is false)
        | Assume of Expression : Expr       //semantics: wp( Stm.Assume(e), phi) := e -> phi
        | Block of Statements: Stm list
        | Choice of Choices : Stm list
        | Write of Variable:Var * Expression:Expr
    
    type Type = SafetySharp.Models.Sam.Type
    type GlobalVarDecl = SafetySharp.Models.Sam.GlobalVarDecl
    type LocalVarDecl = SafetySharp.Models.Sam.LocalVarDecl
 
    type Pgm = {
        Globals : GlobalVarDecl list
        Locals : LocalVarDecl list
        Body : Stm
    }

    let rec translateStm (stm : SafetySharp.Models.Sam.Stm) : Stm =
        match stm with
            | SafetySharp.Models.Sam.Stm.Block(statements) ->
                Stm.Block(statements |> List.map translateStm)
            | SafetySharp.Models.Sam.Stm.Choice (clauses) ->
                let translateClause ( clause :SafetySharp.Models.Sam.Clause) : Stm =
                    Stm.Block([Stm.Assume(clause.Guard);translateStm clause.Statement]) // the guard is now an assumption
                Stm.Choice(clauses |> List.map translateClause)
            | SafetySharp.Models.Sam.Stm.Write (variable,expression) ->
                Stm.Write (variable,expression)

    let translatePgm (pgm : SafetySharp.Models.Sam.Pgm ) : Pgm =
        {
            Pgm.Globals = pgm.Globals;
            Pgm.Locals = pgm.Locals;
            Pgm.Body = translateStm pgm.Body;
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

    