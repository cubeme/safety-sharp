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

// The idea here is to
//   1st: Push every assignment to the end
//   2nd: Push every stochastic statement before the assignments. Merge stochastic statements
//   3rd: Push every choice to the beginning. Merge choices.
// Result: Choice* of (Assume*, Prob of (Assign*)) <--- exactly what we want


module internal VcGuardWithAssignmentModel =
    open SafetySharp.Models
    open SafetySharp.Models.SamHelpers
    
    type VarDecl = Tsam.GlobalVarDecl
    type Var = Tsam.Var
    type Val = Tsam.Val
    type BOp= Tsam.BOp
    type Expr = Tsam.Expr

    type Traceable = Tsam.Traceable

    type GuardWithAssignments = {        
        Guard : Expr;
        Assignments : Map<Var,Expr>;
    }   
        
    type GuardWithAssignmentModel = {
        Globals : VarDecl list;
        GuardsWithFinalAssignments : GuardWithAssignments list;
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