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

namespace SafetySharp.Analysis.Modelchecking.Boogie

module internal VcSamToBoogie =
    
    open SafetySharp.Workflow
    open SafetySharp.Analysis.VerificationCondition
    open SafetySharp.Analysis.Modelchecking.Boogie
    
    let transformVcSamToBoogie (model:VcSam.Pgm) : BoogieSimplifiedAst.Pgm =    
        let maxLoops = 5
        let globalVars = model.Globals |> List.map (fun gl -> gl.Var)
        let globalVarDecls = []
        
        
        let mainProcedureName = BoogieSimplifiedAst.ProcedureName("Main")
        let loopProcedureName = BoogieSimplifiedAst.ProcedureName("Loop")
        
        ////////////////////
        /// MAIN PROCEDURE
        ////////////////////

        let mainCounterVar = BoogieSimplifiedAst.Var.Var("counter")
        let mainCounterVarDecl =
            {
                BoogieSimplifiedAst.VarDecl.Var = mainCounterVar;
                BoogieSimplifiedAst.VarDecl.Type = BoogieSimplifiedAst.Type.IntType;
            }
        let blockIdLoophead = BoogieSimplifiedAst.BlockId("LoopHead")
        let blockIdEnd = BoogieSimplifiedAst.BlockId("End")
        
        let counterIsZeroExpr =
            BoogieSimplifiedAst.Expr.BExpr(BoogieSimplifiedAst.Expr.Read(mainCounterVar),BoogieSimplifiedAst.BOp.Equals,BoogieSimplifiedAst.Expr.Literal(BoogieSimplifiedAst.Val.NumbVal(bigint 0)))
        let initialAssumption =
            //TODO: Make initial values an assumption
            counterIsZeroExpr            
        let mainBlockLoopHead =
            let counterIsLessThanMaxLoops = BoogieSimplifiedAst.Expr.BExpr(BoogieSimplifiedAst.Expr.Read(mainCounterVar),BoogieSimplifiedAst.BOp.Less,BoogieSimplifiedAst.Expr.Literal(BoogieSimplifiedAst.Val.NumbVal(bigint maxLoops)))
            {
                BoogieSimplifiedAst.CodeBlock.BlockId = blockIdLoophead;
                BoogieSimplifiedAst.CodeBlock.Statements =
                    [
                        BoogieSimplifiedAst.Stm.Assume(counterIsLessThanMaxLoops);
                        BoogieSimplifiedAst.Stm.Write(mainCounterVar,BoogieSimplifiedAst.Expr.BExpr(BoogieSimplifiedAst.Expr.Read(mainCounterVar),BoogieSimplifiedAst.BOp.Add,BoogieSimplifiedAst.Expr.Literal(BoogieSimplifiedAst.Val.NumbVal(bigint 1))));
                        BoogieSimplifiedAst.Stm.Call(loopProcedureName,[]);
                    ];
                BoogieSimplifiedAst.CodeBlock.Transfer = BoogieSimplifiedAst.Transfer.Goto([blockIdLoophead;blockIdEnd]);
            }
        let mainBlockLoopEnd =
            let counterIsMaxLoops = BoogieSimplifiedAst.Expr.BExpr(BoogieSimplifiedAst.Expr.Read(mainCounterVar),BoogieSimplifiedAst.BOp.Equals,BoogieSimplifiedAst.Expr.Literal(BoogieSimplifiedAst.Val.NumbVal(bigint maxLoops)))
            {
                BoogieSimplifiedAst.CodeBlock.BlockId = blockIdEnd;
                BoogieSimplifiedAst.CodeBlock.Statements = [BoogieSimplifiedAst.Stm.Assume(counterIsMaxLoops)];
                BoogieSimplifiedAst.CodeBlock.Transfer = BoogieSimplifiedAst.Transfer.Return(None);
            }
        let mainProcedure =
            {
                BoogieSimplifiedAst.Procedure.ProcedureName = mainProcedureName ;
                BoogieSimplifiedAst.Procedure.Modifies = globalVars;
                BoogieSimplifiedAst.Procedure.Assumes = initialAssumption;
                BoogieSimplifiedAst.Procedure.InParameters = [];
                BoogieSimplifiedAst.Procedure.OutParameters = [];
                BoogieSimplifiedAst.Procedure.LocalVars = [mainCounterVarDecl];
                BoogieSimplifiedAst.Procedure.Blocks = [mainBlockLoopHead;mainBlockLoopEnd];
            }
                    
        ////////////////////
        /// LOOP PROCEDURE
        ////////////////////
        
        let pgmAssumption = BoogieSimplifiedAst.Expr.Literal(BoogieSimplifiedAst.Val.BoolVal(true))
        let pgmLocalVars = model.Locals

        let rec transformExpr (expr:VcSam.Expr) : BoogieSimplifiedAst.Expr =
            match expr with
                | VcSam.Expr.Literal (_val) ->
                    BoogieSimplifiedAst.Expr.Literal (_val)
                | VcSam.Expr.UExpr( _operand,op) ->
                    BoogieSimplifiedAst.Expr.UExpr (transformExpr _operand,op)
                | VcSam.Expr.BExpr (leftExpression,bop,rightExpression) ->
                    BoogieSimplifiedAst.Expr.BExpr (transformExpr leftExpression,bop,transformExpr rightExpression)
                | VcSam.Expr.Read (variable) ->
                    BoogieSimplifiedAst.Expr.Read (variable)
                | VcSam.Expr.ReadOld  (variable) ->
                    failwith "NotSupportedYet"

        let rec transformStm (stm:VcSam.Stm) : BoogieSimplifiedAst.CodeBlock list =
            []

        let loopProcedure =
            {
                BoogieSimplifiedAst.Procedure.ProcedureName = loopProcedureName ;
                BoogieSimplifiedAst.Procedure.Modifies = globalVars;
                BoogieSimplifiedAst.Procedure.Assumes = pgmAssumption;
                BoogieSimplifiedAst.Procedure.InParameters = [];
                BoogieSimplifiedAst.Procedure.OutParameters = [];
                BoogieSimplifiedAst.Procedure.LocalVars = pgmLocalVars;
                BoogieSimplifiedAst.Procedure.Blocks = [];
            }

        ////////////////////
        /// Complete Program
        ////////////////////
        
        let boogiePgm =
            {
                BoogieSimplifiedAst.Pgm.GlobalVars = [];
                BoogieSimplifiedAst.Pgm.Procedures = [mainProcedure;loopProcedure];
            }

        boogiePgm
    
    
    
    let transformVcSamToBoogieWf : WorkflowFunction<VcSam.Pgm,BoogieSimplifiedAst.Pgm,unit> = workflow {
        let! vcsamModel = VcSamWorkflow.getVcSamModel
        let newBoogieAst = transformVcSamToBoogie vcsamModel
        do! updateState newBoogieAst        
    }