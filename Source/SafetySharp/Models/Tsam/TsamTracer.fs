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

module internal TsamMutable =

    open SafetySharp.ITracing
    open SafetySharp.Models.TsamHelpers

    type MutablePgm<'traceableOfOrigin> = {
        Pgm : Tsam.Pgm;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Tsam.Traceable;
    }
        with
            interface ITracing<Tsam.Pgm,'traceableOfOrigin,Tsam.Traceable,MutablePgm<'traceableOfOrigin>> with
                member this.getModel = this.Pgm
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Sam.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Sam.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : Tsam.Traceable list =
                    this.Pgm.getTraceables
                    
    open SafetySharp.Workflow
        
    type TsamWorkflowFunction<'traceableOfOrigin,'returnType> =
        WorkflowFunction<MutablePgm<'traceableOfOrigin>,MutablePgm<'traceableOfOrigin>,'returnType>
            
    let getTsamModel ()
            : TsamWorkflowFunction<_,Tsam.Pgm> = workflow {
        let! state = getState ()
        return state.Pgm
    }

    let updateTsamModel<'traceableOfOrigin> (pgm:Tsam.Pgm)
            : EndogenousWorkflowFunction<MutablePgm<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let tsamMutable =
            {
                MutablePgm.Pgm = pgm;
                MutablePgm.TraceablesOfOrigin = state.TraceablesOfOrigin;
                MutablePgm.ForwardTracer = state.ForwardTracer;
            }
        do! updateState tsamMutable
    }
    
    let unnestBlocks<'traceableOfOrigin> ()
            : EndogenousWorkflowFunction<MutablePgm<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let newPgm =
            { state.Pgm with
                Tsam.Pgm.Body = state.Pgm.Body.unnestBlocks (state.Pgm.UniqueStatementIdGenerator)
            }
        let tsamMutable =
            {
                MutablePgm.Pgm = newPgm;
                MutablePgm.TraceablesOfOrigin = state.TraceablesOfOrigin;
                MutablePgm.ForwardTracer = state.ForwardTracer;
            }
        do! updateState tsamMutable
    }
    
    let treeifyStm<'traceableOfOrigin> ()
            : EndogenousWorkflowFunction<MutablePgm<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let newPgm =
            { state.Pgm with
                Tsam.Pgm.Body = state.Pgm.Body.treeifyStm (state.Pgm.UniqueStatementIdGenerator)
            }
        let tsamMutable =
            {
                MutablePgm.Pgm = newPgm;
                MutablePgm.TraceablesOfOrigin = state.TraceablesOfOrigin;
                MutablePgm.ForwardTracer = state.ForwardTracer;
            }
        do! updateState tsamMutable
    }

    let prependKeepValueAssignments<'traceableOfOrigin> ()
            : EndogenousWorkflowFunction<MutablePgm<'traceableOfOrigin>> = workflow {
        // Find every global variable, which was not written to. Prepend statements which keep their value.
        // This is useful for the SSA-Form to express that a variable should keep its value.
        let! state = getState ()
        assert (state.Pgm.CodeForm = Tsam.CodeForm.Default)

        let rec varsWrittenTo (acc:Set<Tsam.Var>) (stm:Tsam.Stm) =
            match stm with
                | Tsam.Stm.Assert _ ->
                    acc
                | Tsam.Stm.Assume _ ->
                    acc
                | Tsam.Stm.Block (sid,statements) ->
                    let newAccs = statements |> List.map (varsWrittenTo acc)
                    newAccs |> Set.unionMany
                | Tsam.Stm.Choice (sid,choices) ->
                    let newAccs = choices |> List.map (varsWrittenTo acc)
                    newAccs |> Set.unionMany
                | Tsam.Stm.Stochastic (sid,stochasticChoices) ->
                    let newAccs = stochasticChoices |> List.map (fun (_,stochasticStm) -> (varsWrittenTo acc stochasticStm))
                    newAccs |> Set.unionMany
                | Tsam.Stm.Write (sid,_var,expr) ->
                    acc.Add _var

        let globalVarSet = state.Pgm.Globals |> List.map (fun gl -> gl.Var) |> Set.ofList
        let varsToAddStatementsFor = Set.difference globalVarSet (varsWrittenTo (Set.empty<Tsam.Var>) (state.Pgm.Body) ) |> Set.toList
        let statementsToPrepend =
            let createAssignment (_var:Tsam.Var) =
                Tsam.Stm.Write(state.Pgm.UniqueStatementIdGenerator (),_var,Tsam.Expr.Read(_var))
            varsToAddStatementsFor |> List.map createAssignment

        let newBody = state.Pgm.Body.prependStatements state.Pgm.UniqueStatementIdGenerator statementsToPrepend

        let newPgm =
            { state.Pgm with
                Tsam.Pgm.Body = newBody
            }
        let tsamMutable =
            {
                MutablePgm.Pgm = newPgm;
                MutablePgm.TraceablesOfOrigin = state.TraceablesOfOrigin;
                MutablePgm.ForwardTracer = state.ForwardTracer;
            }
        do! updateState tsamMutable
    }