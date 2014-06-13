module PromelaAstHelpers

open PromelaDataStructures.Ast

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

let activeProctypeWithNameAndSequence name sequence =
    Proctype.Proctype(Option.Some(Active.Active(None)),name,None,None,None,sequence)

let statementsToSequence (stmnts:Stmnt list) :Sequence =
    stmnts |> List.map (fun elem ->Step.StmntStep(elem,None))
           |> Sequence.Sequence