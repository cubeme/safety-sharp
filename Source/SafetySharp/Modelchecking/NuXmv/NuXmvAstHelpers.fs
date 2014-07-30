namespace SafetySharp.Internal.Modelchecking.NuXmv

module internal NuXmvAstHelpers =

    let concatenateWithOr (exprs:BasicExpression list) =
        if exprs.IsEmpty then
            BasicExpression.ConstExpression(ConstExpression.BooleanConstant(true))
        else
            exprs.Tail |> List.fold (fun acc elem -> BasicExpression.BinaryExpression(elem,BinaryOperator.LogicalOr,acc)) exprs.Head
    let concatenateWithAnd (exprs:BasicExpression list) =
        if exprs.IsEmpty then
            BasicExpression.ConstExpression(ConstExpression.BooleanConstant(false))
        else
            exprs.Tail |> List.fold (fun acc elem -> BasicExpression.BinaryExpression(elem,BinaryOperator.LogicalAnd,acc)) exprs.Head