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

module internal TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables =
    open Tsam
    open TsamHelpers
    open SafetySharp.EngineOptions
    open SafetySharp.Ternary

        
    let rec forceExprToBeInRangeOfVar (varToType:Map<Var,Type>) (_var:Var) (expr:Expr)=
        let rangeOfVar = varToType.Item _var            
        let newExpr_clampOverflow (minValue:Val) (maxValue:Val) : Expr =
            let minValue = Expr.Literal(minValue)
            let maxValue = Expr.Literal(maxValue)
            let greaterEqualMaxThenMaxElse (elseExpr:Expr) =
                Expr.IfThenElseExpr(Expr.BExpr(expr,BOp.GreaterEqual,maxValue),maxValue,elseExpr )
            let lessEqualMinThenMinElse (elseExpr:Expr) =
                Expr.IfThenElseExpr(Expr.BExpr(expr,BOp.LessEqual,minValue),minValue,elseExpr )
            (lessEqualMinThenMinElse (greaterEqualMaxThenMaxElse expr) )
            //((greaterEqualMaxThenMaxElse expr) )
        let newExpr_wrapAround_int_modSemantics (minValue:int) (maxValue:int) : Expr =
            // Note and TODO: If a language supports a bit-Vector, the transformation could be easier more efficient.
            // Examples, if we use a mod-Semantics (length of minValue..maxValue is never negative) :
            //    1. Range from (0..10). Value = 12 => Value = 1
            //    2. Range from (-10..10). Value = -12 => Value = 9
            //    3. Range from (-10..10). Value = 12 => Value = -9
            //    4. Range from (-10..-5). Value = 12 => Value = -9
            //    5. Range from (5..10). Value = 12 => Value = 7
            let rangeWidth = 1 + maxValue - minValue
            // TODO: Formula: something like: (distance(minValue,value) % rangeLength) + minValue
            failwith "To determine"

        let newExpr_wrapAround_reset (minValue:Val) (maxValue:Val) : Expr =
            let minValue = Expr.Literal(minValue)
            let maxValue = Expr.Literal(maxValue)
            let greaterMaxThenMinElse (elseExpr:Expr) =
                Expr.IfThenElseExpr(Expr.BExpr(expr,BOp.Greater,maxValue),minValue,elseExpr )
            let lessMinThenMaxElse (elseExpr:Expr) =
                Expr.IfThenElseExpr(Expr.BExpr(expr,BOp.Less,minValue),maxValue,elseExpr )
            (lessMinThenMaxElse (greaterMaxThenMinElse expr) )

        match rangeOfVar with
            | Type.BoolType
            | Type.IntType 
            | Type.RealType  ->
                expr
            | Type.RangedIntType (_from,_to,overflowBehavior) ->
                let minValue = Val.NumbVal(bigint _from)
                let maxValue = Val.NumbVal(bigint _to)
                match overflowBehavior with
                    | OverflowBehavior.Clamp ->
                        newExpr_clampOverflow minValue maxValue
                    | OverflowBehavior.Error ->
                        expr
                    | OverflowBehavior.WrapAround ->
                        newExpr_wrapAround_reset minValue maxValue
                    | _ ->
                        failwith "not determined what it means, yet"
            | Type.RangedRealType (_from,_to,overflowBehavior) ->
                let minValue = Val.RealVal(_from)
                let maxValue = Val.RealVal(_to)
                match overflowBehavior with
                    | OverflowBehavior.Clamp ->
                        newExpr_clampOverflow minValue maxValue
                    | OverflowBehavior.Error ->
                        expr
                    | OverflowBehavior.WrapAround ->
                        //failwith "make either modulo or start with min. Modulo makes no sense for real types. To determine"
                        newExpr_wrapAround_reset minValue maxValue
                    | _ ->
                        failwith "not determined what it means, yet"
                        
    let rec applyAssignmentSemanticsAfterAssignment (pgm:Pgm) : Pgm =
        let varToType =
            pgm.VarToType
        //    let varToTypeWithGlobals = pgm.Globals |> List.fold (fun (acc:Map<Tsam.Var,Tsam.Type>) elem -> acc.Add(elem.Var,elem.Type)) (Map.empty<Tsam.Var,Tsam.Type>)
        //    let varToTypeWithGlobalsAndLocals = pgm.Locals |> List.fold (fun (acc:Map<Tsam.Var,Tsam.Type>) elem -> acc.Add(elem.Var,elem.Type)) (varToTypeWithGlobals)
        //    varToTypeWithGlobalsAndLocals
        let rec applyToStm (stm:Stm) : Stm =
            match stm with
                | Stm.Assert (sid,expr) ->
                    stm
                | Stm.Assume (sid,expr) ->
                    stm
                | Stm.Block (sid,statements) ->
                    let newStmnts = statements |> List.map applyToStm
                    Stm.Block (sid,newStmnts)
                | Stm.Choice (sid,choices) ->
                    let newChoices = choices |> List.map (fun (choiceGuard,choiceStm) -> (choiceGuard,applyToStm choiceStm))
                    Stm.Choice (sid,newChoices)
                | Stm.Stochastic (sid,stochasticChoices) ->
                    let newChoices = stochasticChoices |> List.map (fun (stochasticExpr,stochasticStm) -> (stochasticExpr,applyToStm stochasticStm))
                    Stm.Stochastic (sid,newChoices)
                | Stm.Write (sid,_var,expr) ->
                    Stm.Write (sid,_var,forceExprToBeInRangeOfVar varToType _var expr)
        { pgm with
            Pgm.Body = applyToStm pgm.Body
            Pgm.Attributes = {pgm.Attributes with Attributes.SemanticsOfAssignmentToRangedVariablesAppliedExplicitly=Ternary.True;}
        }

                
    let applyAssignmentSemanticsAfterStep (pgm:Pgm) : Pgm =
        let newStatements =
            let createRangedAssignment (globalVarDecl:GlobalVarDecl) : Stm =
                let rangedVarExpression = forceExprToBeInRangeOfVar (pgm.VarToType) (globalVarDecl.Var) (Expr.Read(globalVarDecl.Var))
                Stm.Write(pgm.UniqueStatementIdGenerator (),globalVarDecl.Var,rangedVarExpression)
            
            do pgm.Globals |> List.iter (fun globalVar -> assert ( (pgm.NextGlobal.Item (globalVar.Var)) = (globalVar.Var))  ) // TODO: currently stupid check here is necessary to avoid false use
            
            pgm.Globals |> List.map createRangedAssignment
        
        let newBody = pgm.Body.appendStatements (pgm.UniqueStatementIdGenerator) (newStatements)
        { pgm with
            Pgm.Body = newBody
            Pgm.Attributes =
                { pgm.Attributes with
                    Attributes.SemanticsOfAssignmentToRangedVariablesAppliedExplicitly=Ternary.True;
                    Attributes.IsSingleAssignment = Ternary.Unknown;
                }
        }


    let applySemanticsToPgm (semanticsOfAssignmentToRangedVariables:TsamEngineOptions.SemanticsOfAssignmentToRangedVariables)
                            (pgm:Pgm) =

        let newPgm =
            match semanticsOfAssignmentToRangedVariables with
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.IgnoreRanges ->
                    { pgm with
                        Pgm.Attributes = {pgm.Attributes with Attributes.SemanticsOfAssignmentToRangedVariablesAppliedExplicitly=Ternary.True;}
                    }
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangeAfterEveryAssignmentToAGlobalVar ->
                    applyAssignmentSemanticsAfterAssignment pgm
                | TsamEngineOptions.SemanticsOfAssignmentToRangedVariables.ForceRangesAfterStep ->
                    applyAssignmentSemanticsAfterStep pgm
                | _ ->
                    failwith "Not possible to apply the selected semantics of the EngineOption TsamEngineOptions.SemanticsOfAssignmentToRangedVariables, yet."
                    
        newPgm
        
    open SafetySharp.Workflow
    open SafetySharp.Models.TsamMutable

    let applySemanticsWorkflow<'traceableOfOrigin> ()
            : EndogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>> = workflow {
        let! semanticsOfAssignmentToRangedVariables =
            getEngineOption<_,TsamEngineOptions.SemanticsOfAssignmentToRangedVariables> ()

        let! state = getState ()
        let pgm = state.Pgm
        if (pgm.Attributes.SemanticsOfAssignmentToRangedVariablesAppliedExplicitly <> Ternary.True) then
            let newState = {state with Pgm = (applySemanticsToPgm semanticsOfAssignmentToRangedVariables pgm) }
            do! updateState newState
        else
            ()
    }