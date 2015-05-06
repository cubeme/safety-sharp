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

// TODO: This is currently only a draft of an idea

// The idea here is to transform the Tsam to a form, which resembles the guard with assignment form.
//   1st: Push every assignment to the end
//   2nd: Push every stochastic statement before the assignments (or to end, if none exists). Merge stochastic statements
//   3rd: Pull every choice to the beginning. Merge choices.
// TODO: Empty Blocks and nested blocks are difficult to treat. Maybe write a normalizer to facilitate this step.
// Result: Choice* of (Assume*, Prob of (Assign*)) <--- exactly what we want


module internal VcGuardWithAssignmentModel =
    open SafetySharp.Models
    open SafetySharp.Models.TsamHelpers
    
    type VarDecl = Tsam.GlobalVarDecl
    type Var = Tsam.Var
    type Val = Tsam.Val
    type BOp= Tsam.BOp
    type Expr = Tsam.Expr

    type Traceable = Tsam.Traceable

    open SafetySharp.Workflow
    open SafetySharp.Models.Tsam
    open SafetySharp.Models.TsamMutable

    let phase1FindAssignmentNotAtTheEnd () : TsamWorkflowFunction<_,StatementId option> = workflow {
        //returns StatementId and type of next statement. type of the next statement should not be assignment
        return None
    }
    
    let phase1PushAssignmentOverChoice (stmId:StatementId) : TsamWorkflowFunction<_,unit> = workflow {
        return ()
    }
        
    let phase1PushAssignmentOverStochastic (stmId:StatementId) : TsamWorkflowFunction<_,unit> = workflow {
        return ()
    }
        
    let phase1PushAssignmentOverAssumption (stmId:StatementId) : TsamWorkflowFunction<_,unit> = workflow {
        return ()
    }

    let phase1PushAssignmentOverAssertion (stmId:StatementId) : TsamWorkflowFunction<_,unit> = workflow {
        return ()
    }

    let phase1PushAssignmentTowardsEnd () : TsamWorkflowFunction<_,unit> = workflow {
        let! (a) = phase1FindAssignmentNotAtTheEnd ()
        match a with
            | None -> return ()
            | Some(stmId) ->
                do! phase1PushAssignmentOverChoice stmId
    }

    let phase2PushStochasticTowardsEnd () : TsamWorkflowFunction<_,unit> = workflow {
        let! (a) = phase1FindAssignmentNotAtTheEnd ()
        match a with
            | None -> return ()
            | Some(stmId) ->
                do! phase1PushAssignmentOverChoice stmId
    }

    let phase3PullChoicesTowardsBeginning () : TsamWorkflowFunction<_,unit> = workflow {
        let! (a) = phase1FindAssignmentNotAtTheEnd ()
        match a with
            | None -> return ()
            | Some(stmId) ->
                do! phase1PushAssignmentOverChoice stmId
    }

    let transformTsamToTsamInGuardToAssignmentForm () : TsamWorkflowFunction<_,unit> = workflow {
        do! iterateToFixpoint (phase1PushAssignmentTowardsEnd ())
        do! iterateToFixpoint (phase2PushStochasticTowardsEnd ())
        do! iterateToFixpoint (phase3PullChoicesTowardsBeginning ())
        return ()
    }
    

    type GuardWithAssignments = {        
        Guard : Expr;
        Assignments : Map<Var,Expr>;
    }   
        
    type GuardWithAssignmentModel = {
        Globals : VarDecl list;
        GuardsWithFinalAssignments : GuardWithAssignments list;
    }
    
    let transformGwaTsamToGwaModel (pgm:Tsam.Pgm) : GuardWithAssignmentModel =
        {
            GuardWithAssignmentModel.Globals = [];
            GuardWithAssignmentModel.GuardsWithFinalAssignments = [];
        }

    open SafetySharp.ITracing

    type GuardWithAssignmentModelTracer<'traceableOfOrigin> = {
        GuardWithAssignmentModel : GuardWithAssignmentModel;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Tsam.Traceable;
    }
        with
            interface ITracing<GuardWithAssignmentModel,'traceableOfOrigin,Tsam.Traceable,GuardWithAssignmentModelTracer<'traceableOfOrigin>> with
                member this.getModel = this.GuardWithAssignmentModel
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Sam.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Sam.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : Tsam.Traceable list =
                    this.GuardWithAssignmentModel.Globals |> List.map (fun varDecl -> Traceable.Traceable(varDecl.Var))
                    
                    
    let transformWorkflow<'traceableOfOrigin> () : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,GuardWithAssignmentModelTracer<'traceableOfOrigin>> = workflow {
        do! transformTsamToTsamInGuardToAssignmentForm ()

        let! state = getState ()
        let model = state.Pgm
        let transformed =
            {
                GuardWithAssignmentModelTracer.GuardWithAssignmentModel = transformGwaTsamToGwaModel model;
                GuardWithAssignmentModelTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                GuardWithAssignmentModelTracer.ForwardTracer = state.ForwardTracer;
            }
        do! updateState transformed
    }