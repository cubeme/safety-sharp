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
    
    type HybridCodeBlock = {
        //same as a BoogieSimplifiedAst.CodeBlock but with VcSam Statements
        BlockId : BoogieSimplifiedAst.BlockId
        Statements : VcSam.Stm list;
        Transfer : BoogieSimplifiedAst.Transfer;
    }
    
    type TransformationContext =
        {
            HybridCodeBlocksReverse : HybridCodeBlock list;
        }
            with
                member this.appendHybridCodeBlock (entry:HybridCodeBlock) =
                    { this with
                        TransformationContext.HybridCodeBlocksReverse = entry :: this.HybridCodeBlocksReverse;
                    }
                member this.getHybridCodeBlocks =
                    this.HybridCodeBlocksReverse |> List.rev
                member this.getBlockIdForVcStmBlock (blockStmId:VcSam.StatementId) (part:int) =
                    BoogieSimplifiedAst.BlockId(sprintf "Block%dPart%d" blockStmId.Value part)        
                member this.getBlockIdForVcStmNonBlock (blockStmId:VcSam.StatementId) =
                    BoogieSimplifiedAst.BlockId(sprintf "NonBlock%d" blockStmId.Value)
                static member initial = 
                    {
                        TransformationContext.HybridCodeBlocksReverse = [];
                    }


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



        let rec createTransformationContext (returnTo:BoogieSimplifiedAst.Transfer) (context:TransformationContext) (stm:VcSam.Stm) : TransformationContext =
            // A list of statements can be split up into groups of 'chained atomar statements' (HybridCodeBlock.Statements), 'block stm' (BS) and 'choice stm' (CS).
            let processStmBlock (returnTo:BoogieSimplifiedAst.Transfer) (context:TransformationContext) (blockStmId:VcSam.StatementId,stmts:VcSam.Stm list) : TransformationContext =
                // we swapped the extraction of CASs in an Block-Statement, which is the most complex processing of all statements
                let context = ref context
                let currentPart = ref 1
                let currentBlockId = ref (context.Value.getBlockIdForVcStmBlock blockStmId currentPart.Value)
                let currentCASrev = ref ([])
                let processStmInBlock (stm:VcSam.Stm) : unit  =
                    match stm with
                        | VcSam.Stm.Assert (sid,expr) ->
                            currentCASrev := stm::currentCASrev.Value
                        | VcSam.Stm.Assume (sid,expr) ->
                            currentCASrev := stm::currentCASrev.Value
                        | VcSam.Stm.Write (sid,variable,expression) ->
                            currentCASrev := stm::currentCASrev.Value
                        | VcSam.Stm.Block (sid,_) ->
                            let statementBlockId = context.Value.getBlockIdForVcStmNonBlock stm.GetStatementId
                            let transferToBlock = BoogieSimplifiedAst.Transfer.Goto([statementBlockId])
                            // create HybridCodeBlock for all atomic statements until now
                            let hybridCodeBlock =
                                {
                                    HybridCodeBlock.BlockId = currentBlockId.Value;
                                    HybridCodeBlock.Statements = currentCASrev.Value |> List.rev;
                                    HybridCodeBlock.Transfer = transferToBlock;
                                }
                            context := context.Value.appendHybridCodeBlock hybridCodeBlock
                            // now process the block
                            let nextPart = currentPart.Value + 1
                            let nextBlockId = context.Value.getBlockIdForVcStmBlock blockStmId nextPart
                            let transferToNextBlockId = BoogieSimplifiedAst.Transfer.Goto([nextBlockId])
                            // create for blockstms new blocks (even if it's not necessary and could be inlined. makes the algorithm easier to read)
                            context := createTransformationContext transferToNextBlockId context.Value stm
                            // reset all collected information and start next part of the block
                            currentPart := nextPart
                            currentBlockId := nextBlockId
                            currentCASrev := []
                            ()
                        | VcSam.Stm.Choice (sid,choices) ->
                            let choicesBlockIds = choices |> List.map (fun selected -> context.Value.getBlockIdForVcStmNonBlock selected.GetStatementId)
                            let transferToChoices = choicesBlockIds |> BoogieSimplifiedAst.Transfer.Goto
                            // create HybridCodeBlock for all atomic statements until now
                            let hybridCodeBlock =
                                {
                                    HybridCodeBlock.BlockId = currentBlockId.Value;
                                    HybridCodeBlock.Statements = currentCASrev.Value |> List.rev;
                                    HybridCodeBlock.Transfer = transferToChoices;
                                }
                            context := context.Value.appendHybridCodeBlock hybridCodeBlock
                            // now process the block
                            let nextPart = currentPart.Value + 1
                            let nextBlockId = context.Value.getBlockIdForVcStmBlock blockStmId nextPart
                            let transferToNextBlockId = BoogieSimplifiedAst.Transfer.Goto([nextBlockId])
                            context := createTransformationContext transferToNextBlockId context.Value stm
                            // reset all collected information and start next part of the block
                            currentPart := nextPart
                            currentBlockId := nextBlockId
                            currentCASrev := []
                            ()
                List.iter processStmInBlock stmts
                let lastHybridCodeBlock =
                    {
                        HybridCodeBlock.BlockId = currentBlockId.Value;
                        HybridCodeBlock.Statements = currentCASrev.Value |> List.rev
                        HybridCodeBlock.Transfer = returnTo;
                    }
                context := context.Value.appendHybridCodeBlock lastHybridCodeBlock
                context.Value
            // until now was the extraction of CASs in a block in a swapped function
            let processStmNonBlock (returnTo:BoogieSimplifiedAst.Transfer) (context:TransformationContext) (stm:VcSam.Stm) : TransformationContext =
                // create an own HybridCodeBlock only for this single statement
                let currentBlockId = context.getBlockIdForVcStmNonBlock stm.GetStatementId
                let hybridCodeBlock =
                    {
                        HybridCodeBlock.BlockId = currentBlockId;
                        HybridCodeBlock.Statements = [stm];
                        HybridCodeBlock.Transfer = returnTo;
                    }
                context.appendHybridCodeBlock hybridCodeBlock
            // now we actually do something
            match stm with
                | VcSam.Stm.Assert _ ->
                    processStmNonBlock returnTo context stm
                | VcSam.Stm.Assume _ ->
                    processStmNonBlock returnTo context stm
                | VcSam.Stm.Write _ ->
                    processStmNonBlock returnTo context stm
                | VcSam.Stm.Block (sid,stmts) ->
                    // When a statement refers to a block statement, it refers to the compound block (i.e. the stm containing the other statements).
                    // Thus, we must make a redirection from this compound block to the first part of the block.
                    // We could also make a transfer everywhere directly into the code block. But there a several side conditions to take care of.
                    // Note: The sub statements of this block should return to the position where this block should actually return to.
                    let compoundBlock_BlockId = context.getBlockIdForVcStmNonBlock stm.GetStatementId
                    let firstPartInBlock_BlockId = context.getBlockIdForVcStmBlock stm.GetStatementId 1
                    // the transfer to this block was done by a transfer to 'compoundBlock_BlockId'
                    let firstPartInBlockTransfer = BoogieSimplifiedAst.Transfer.Goto([firstPartInBlock_BlockId])                    
                    let hybridCodeBlock =
                        {
                            HybridCodeBlock.BlockId = compoundBlock_BlockId;
                            HybridCodeBlock.Statements = []; //do nothing.
                            HybridCodeBlock.Transfer = firstPartInBlockTransfer;
                        }
                    let context = context.appendHybridCodeBlock hybridCodeBlock
                    processStmBlock returnTo context (sid,stmts)
                | VcSam.Stm.Choice (sid,choices) ->
                    let newContext = List.fold (createTransformationContext returnTo) context choices
                    newContext
                        
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

        let transformHybridCodeBlock (entry:HybridCodeBlock) : BoogieSimplifiedAst.CodeBlock =
            let transformAtomicStatement (stm:VcSam.Stm) : BoogieSimplifiedAst.Stm =
                match stm with
                    | VcSam.Stm.Assert (sid,expr) ->
                        BoogieSimplifiedAst.Stm.Assert(transformExpr expr)
                    | VcSam.Stm.Assume (sid,expr) ->
                        BoogieSimplifiedAst.Stm.Assume(transformExpr expr)
                    | VcSam.Stm.Write (sid,var,expr) ->
                        BoogieSimplifiedAst.Stm.Write(var,transformExpr expr)
                    | _ ->
                        failwith "Stm.Choice or Stm.Block should not be here in this stage"
            {
                BoogieSimplifiedAst.CodeBlock.BlockId = entry.BlockId;
                BoogieSimplifiedAst.CodeBlock.Statements = entry.Statements |> List.map transformAtomicStatement;
                BoogieSimplifiedAst.CodeBlock.Transfer = entry.Transfer;
            }
                    
        let transformPgm (stm:VcSam.Stm) : BoogieSimplifiedAst.CodeBlock list =
            let hybridCodeBlocks = createTransformationContext (BoogieSimplifiedAst.Transfer.Return(None)) TransformationContext.initial stm
            let transformedCodeBlocks = hybridCodeBlocks.getHybridCodeBlocks |> List.map transformHybridCodeBlock
            transformedCodeBlocks

        let loopProcedure =
            {
                BoogieSimplifiedAst.Procedure.ProcedureName = loopProcedureName ;
                BoogieSimplifiedAst.Procedure.Modifies = globalVars;
                BoogieSimplifiedAst.Procedure.Assumes = pgmAssumption;
                BoogieSimplifiedAst.Procedure.InParameters = [];
                BoogieSimplifiedAst.Procedure.OutParameters = [];
                BoogieSimplifiedAst.Procedure.LocalVars = pgmLocalVars;
                BoogieSimplifiedAst.Procedure.Blocks = transformPgm model.Body;
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