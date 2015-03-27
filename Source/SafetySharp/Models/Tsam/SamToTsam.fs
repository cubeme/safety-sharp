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

namespace SafetySharp.Analysis.VerificationCondition

module internal VcTransformSamToVcSam =
    open SafetySharp.Workflow

    
    open SafetySharp.Workflow

    
    type VcSamPgm = VcSam.Pgm



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
                        do stmIdCounter := stmIdCounter.Value + 1
                        let freshIdForAssertion = Some(stmIdCounter.Value)
                        (VcSam.Stm.Assert(freshIdForAssertion,VcSam.Expr.Literal(VcSam.Val.BoolVal(true))))
                    let translateClause ( clause :SafetySharp.Models.Sam.Clause) : VcSam.Stm =
                        do stmIdCounter := stmIdCounter.Value + 1
                        let freshIdForGuard = Some(stmIdCounter.Value)
                        do stmIdCounter := stmIdCounter.Value + 1
                        let freshIdForBlock = Some(stmIdCounter.Value)
                        VcSam.Stm.Block(freshIdForBlock,[VcSam.Stm.Assume(freshIdForGuard,clause.Guard);translateStm stmIdCounter clause.Statement]) // the guard is now an assumption
                    VcSam.Stm.Choice(freshId,clauses |> List.map translateClause)
            | SafetySharp.Models.Sam.Stm.Write (variable,expression) ->
                VcSam.Stm.Write (freshId,variable,expression)
                
    let translatePgm (stmIdCounter:int ref) (pgm : SafetySharp.Models.Sam.Pgm ) : VcSam.Pgm =
        let nextGlobals =
            pgm.Globals |> List.map (fun varDecl -> (varDecl.Var,varDecl.Var) ) //map to the same variable
                        |> Map.ofList
        let uniqueStatementIdGenerator =
            let stmIdCounter : int ref = ref 0 // this stays in the closure
            let generator () : VcSam.StatementId =
                do stmIdCounter := stmIdCounter.Value + 1
                failwith "currently not used. need to convert old code first"
                VcSam.StatementId.Some(stmIdCounter.Value)
            generator
        {
            VcSam.Pgm.Globals = pgm.Globals;
            VcSam.Pgm.Locals = pgm.Locals;
            VcSam.Pgm.Body = translateStm stmIdCounter pgm.Body;
            VcSam.Pgm.NextGlobal = nextGlobals;
            VcSam.Pgm.CodeForm = VcSam.CodeForm.MultipleAssignments;
            VcSam.Pgm.UsedFeatures = ();
            VcSam.Pgm.UniqueStatementIdGenerator = uniqueStatementIdGenerator
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