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

//  * http://en.wikipedia.org/wiki/Predicate_transformer_semantics
//  * [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904

module internal VcStrongestPostcondition =
    open VcSam
        
    open VcSam
    open SafetySharp.Models.SamHelpers
    // Predicate Transformers
      
    (*
    let rec sp_rewriteExpr_varsToExpr (variable:Var,toExpr:Expr) (expr:Expr): Expr =
        match expr with
            | Expr.Literal (_val) -> Expr.Literal(_val)
            | Expr.Read (_var) -> if _var = variable then toExpr else expr
            | Expr.ReadOld (_var) -> expr //old variables keep their value
            | Expr.UExpr (expr,uop) -> Expr.UExpr(wp_rewriteExpr_varsToExpr (variable,toExpr) expr ,uop)
            | Expr.BExpr (left, bop, right) -> Expr.BExpr(wp_rewriteExpr_varsToExpr (variable,toExpr) left,bop,wp_rewriteExpr_varsToExpr (variable,toExpr) right)



    // Returns the strongest postcondition of stm and a list of proof obligations that are needed as requirements,
    // that this strongest postcondition is true. If the proof obligations are not fulfilled, the resulting formula
    // is not guaranteed to be valid.
    // These proof obligations mainly originate from assertions.
    // (Weakest Precondition is easier. It doesn't create additional proof obligations)
    // [GCFK09] doesn't need a complicated assignment rule, because the input program is in passive form
    let rec sp (stm:Stm) (previousProofObligations:Expr list) (formula:Expr) : Expr*(Expr list) = 
        match stm with
        | Assert (_,expr) ->
            Expr.BExpr(expr,BOp.And,formula)
        | Assume (_,expr) ->
            Expr.BExpr(expr,BOp.Implies,formula)
        | Block (_,statements) ->
            List.foldBack wp statements formula
        | Choice (_,choices) ->
            let choicesAsExpr =
                choices |> List.map (fun choice -> wp choice formula)               
    *)
