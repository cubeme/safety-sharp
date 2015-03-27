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

//  * http://en.wikipedia.org/wiki/
//  * [CC96] G.C. Gannod, B.H.C. Cheng. Strongest postcondition semantics as the formal basis for reverse engineering.
//                 http://dx.doi.org/10.1109/WCRE.1995.514707
//  * [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904
//  * [HS+11] D. Haneberg, G. Schellhorn, et al. Lecture notes of Formal Methods in Software Engineering
//                 http://www.informatik.uni-augsburg.de/lehrstuehle/swt/se/teaching/fruehere_semester/ss11/FM4SE/Folien/

module internal VcStrongestPostcondition =
    open SafetySharp.Models.Tsam
    open SafetySharp.Models.SamHelpers
    // Predicate Transformers

    // Removal of the quantification in the assignment rule is necessary, to automate the transformation and find a compact formula:
    // Formula for sp:
    //    sp(\phi, x:=e) = (\exists v^{<}. Q{ x \substby  v^{<} } \wedge e{ x \substby  v^{<} } )
    //    v^{<} contains a possible value of the "previous" x. There might be more values, see example.
    //    The x in the expression is replaced by its former value. The \exist collects all former values of
    //    variable x. This is actually needed, when the former value may be a set (example x>=4).
    // Example smokeTest20.sam, first branch:
    // v^{<}
    // { y >= 2 }
    //	    x := 1;
    // { [y >= 2 ] \wedge x = 1}    // the '[' ']' marks Q.
    //	    x := y + 3;
    // { [y >= 2 \wedge 1 = 1 ] \wedge x = y + 3}. The only value for x, which satisfies x=1 is 1. Thus, 1 = 1.
    //	    x := y + x;
    // { [y >= 2 \wedge 1 = 1 \wedge y + 3 = y + 3 ] \wedge x = y + y + 3 }. The only values for x, which satisfies x = y + 3 is y + 3. Thus, y + 3 = y + 3.
    //	    y := x + 2;
    // { ([ 2 >= 2 \wedge 1 = 1 \wedge 2 + 3 = 2 + 3 \wedge x = 2 + 2 + 3] \wedge y = x + 2) \vee 
    //   ([ 3 >= 2 \wedge 1 = 1 \wedge 3 + 3 = 3 + 3 \wedge x = 3 + 3 + 3] \wedge y = x + 2) \vee ... }. There are more possible values for y, which satisfy y >= 2. E.g. 2 >= 2 or 3 >= 2, ... And we cannot find an abbreviation as in the step before. Thus, we have to enumerate them all somehow.
    //      ...
    

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
    // Weakest Precondition is easier. It doesn't create additional proof obligations for assertions and has
    // no exists in the assignment rule. To enable an easy translation, we require passive form. For details on the
    // assignment rule see [CC96].
    // [GCFK09] doesn't need a complicated assignment rule, because the input program is in passive form.
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
