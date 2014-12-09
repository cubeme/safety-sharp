// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Internal.Modelchecking.PromelaSpin

module internal PromelaAstHelpers =

    let skipStatement = Stmnt.ExprStmnt(Expr.AnyExpr(AnyExpr.Const(Const.Skip)))

    let coverInSimpleBlockStatement (stmnts:Stmnt list) : Stmnt =
        let steps = stmnts |> List.map (fun elem -> Step.StmntStep(elem,None))
        Stmnt.SequenceStmnt(Sequence.Sequence(steps))
    
    let coverInDStepBlockStatement (stmnts:Stmnt list) : Stmnt =
        let steps = stmnts |> List.map (fun elem -> Step.StmntStep(elem,None))
        Stmnt.DStepStmnt(Sequence.Sequence(steps))
    
    let coverInAtomicBlockStatement (stmnts:Stmnt list) : Stmnt =
        let steps = stmnts |> List.map (fun elem -> Step.StmntStep(elem,None))
        Stmnt.AtomicStmnt(Sequence.Sequence(steps))

    let stmntToStep (stmnt:Stmnt) : Step =
        Step.StmntStep(stmnt,None)
    
    let exprToStep (expr:Expr) : Step =
        Step.StmntStep(Stmnt.ExprStmnt(expr),None)

    let anyExprToStep (anyExpr:AnyExpr) : Step =
        Step.StmntStep(Stmnt.ExprStmnt(Expr.AnyExpr(anyExpr)),None)

    let anyExprToStmnt (anyExpr:AnyExpr) : Stmnt =
        Stmnt.ExprStmnt (Expr.AnyExpr anyExpr)

    let createAssignmentStatement (target:Varref) (expression:AnyExpr) =
        Assign.AssignExpr(target,expression) |> Stmnt.AssignStmnt

    let activeProctypeWithNameAndSequence name sequence =
        Proctype.Proctype(Option.Some(Active.Active(None)),name,None,None,None,sequence)

    let statementsToSequence (stmnts:Stmnt list) :Sequence =
        stmnts |> List.map (fun elem ->Step.StmntStep(elem,None))
               |> Sequence.Sequence