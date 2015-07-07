// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineeringgineering
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

module internal SamToTsam =
    open SafetySharp.Workflow    
    type TsamPgm = Tsam.Pgm



    let rec translateStm (uniqueStatementIdGenerator : unit -> Tsam.StatementId) (stm : SafetySharp.Models.Sam.Stm) : Tsam.Stm =
        let freshId = uniqueStatementIdGenerator ()
        match stm with
            | SafetySharp.Models.Sam.Stm.Block(statements) ->
                Tsam.Stm.Block(freshId,statements |> List.map (translateStm uniqueStatementIdGenerator) )
            | SafetySharp.Models.Sam.Stm.Choice (clauses) ->                
                if clauses = [] then
                    (Tsam.Stm.Assume(freshId,Tsam.Expr.Literal(Tsam.Val.BoolVal(false))))
                else
                    let atLeastOneGuardIsTrue =                        
                        // TODO: It is not guaranteed, that at least one branch is true
                        // See examples smokeTest17.sam and smokeTest18.sam.
                        // A variant of the formula adds the ored guards to the anded expression.
                        // This ensures, that at least one path is viable. Otherwise the wp returns false.
                        // The difference between a program with this assertion and without:
                        // If no guard matches (not fully specified), the program without assertion returns true
                        // (and thus allows everything. Each variable may have an arbitrary value afterwards).
                        // If no guard matches, the program without assertion returns false
                        // (and thus blocks every execution).
                        // PseudoCode:
                        //     let atLeastOneGuardIsTrue =
                        //         Expr.createOredExpr guardsAsExpr
                        let freshIdForAssertion = uniqueStatementIdGenerator ()
                        (Tsam.Stm.Assert(freshIdForAssertion,Tsam.Expr.Literal(Tsam.Val.BoolVal(true))))
                    let translateClause ( clause :SafetySharp.Models.Sam.Clause) : (Tsam.Expr option*Tsam.Stm) =
                        // TODO: Old Code, could be reused for transformation: 
                        //   let freshIdForGuard = uniqueStatementIdGenerator ()
                        //   let freshIdForBlock = uniqueStatementIdGenerator ()
                        //   Tsam.Stm.Block(freshIdForBlock,[Tsam.Stm.Assume(freshIdForGuard,clause.Guard);translateStm uniqueStatementIdGenerator clause.Statement]) // the guard is now an assumption
                        (Some(clause.Guard),translateStm uniqueStatementIdGenerator clause.Statement)
                    Tsam.Stm.Choice(freshId,clauses |> List.map translateClause)
            | SafetySharp.Models.Sam.Stm.Stochastic (stochasticChoices) -> 
                let translateStochasticChoice ( (probability,stm) : Sam.Expr * Sam.Stm) : Tsam.Expr * Tsam.Stm =
                    (probability,translateStm uniqueStatementIdGenerator stm)
                Tsam.Stm.Stochastic(freshId,stochasticChoices |> List.map translateStochasticChoice)
            | SafetySharp.Models.Sam.Stm.Write (variable,expression) ->
                Tsam.Stm.Write (freshId,variable,expression)
                
    let translatePgm (pgm : SafetySharp.Models.Sam.Pgm ) : Tsam.Pgm =
        let nextGlobals =
            pgm.Globals |> List.map (fun varDecl -> (varDecl.Var,varDecl.Var) ) //map to the same variable
                        |> Map.ofList

        let uniqueStatementIdGenerator =
            let stmIdCounter : int ref = ref 0 // this stays in the closure
            let generator () : Tsam.StatementId =
                do stmIdCounter := stmIdCounter.Value + 1
                Tsam.StatementId(stmIdCounter.Value)
            generator
        {
            Tsam.Pgm.Globals = pgm.Globals;
            Tsam.Pgm.Locals = pgm.Locals;
            Tsam.Pgm.ElementToType = TsamHelpers.createElementToType (pgm.Globals,pgm.Locals);
            Tsam.Pgm.Body = translateStm uniqueStatementIdGenerator pgm.Body;
            Tsam.Pgm.NextGlobal = nextGlobals;
            Tsam.Pgm.CodeForm = Tsam.CodeForm.Default;
            Tsam.Pgm.Attributes = Tsam.Attributes.fullyUnknown;
            Tsam.Pgm.UniqueStatementIdGenerator = uniqueStatementIdGenerator
        }
      
    open SafetySharp.Workflow

    let transformSamToTsam<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<SamTracer.SamTracer<'traceableOfOrigin>,TsamTracer.TsamTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let transformed =
            {
                TsamTracer.TsamTracer.Pgm = translatePgm (state.Pgm);
                TsamTracer.TsamTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                TsamTracer.TsamTracer.ForwardTracer = state.ForwardTracer;
            }
        do! updateState transformed
    }