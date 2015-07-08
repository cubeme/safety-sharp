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

namespace SafetySharp.Models

module ScmVerificationElements =
    open Scm
    
    [<RequireQualifiedAccessAttribute>]
    type PropositionalExpr =
        | Literal of Val
        | ReadField of CompPath * Field
        | ReadFault of CompPath * Fault
        | UExpr of PropositionalExpr * UOp
        | BExpr of PropositionalExpr * BOp * PropositionalExpr
    
    [<RequireQualifiedAccessAttribute>]
    type LuOp =
        | Next
        | Globally
        | Eventually
        
    [<RequireQualifiedAccessAttribute>]
    type LbOp =
        | Until

    [<RequireQualifiedAccessAttribute>]
    type LtlExpr =
        | Literal of Val
        | ReadField of CompPath * Field
        | ReadFault of CompPath * Fault
        | UExpr of LtlExpr * UOp
        | BExpr of LtlExpr * BOp * LtlExpr
        | LuExpr of LtlExpr * LuOp
        | LbExpr of LtlExpr * LbOp * LtlExpr

    let CreateReadField path field =
        LtlExpr.ReadField (path |> Seq.map Comp |> Seq.toList, field |> Field)

    let CreateReadFault path fault =
        LtlExpr.ReadFault (path |> Seq.map Comp |> Seq.toList, fault |> Fault.Fault)

    let rec ToPropositionalFormula = function
        | LtlExpr.Literal l -> PropositionalExpr.Literal l
        | LtlExpr.ReadField (c, f) -> PropositionalExpr.ReadField (c, f)
        | LtlExpr.ReadFault (c, f) -> PropositionalExpr.ReadFault (c, f)
        | LtlExpr.UExpr (e, o) -> PropositionalExpr.UExpr (ToPropositionalFormula e, o)
        | LtlExpr.BExpr (e1, o, e2) -> PropositionalExpr.BExpr (ToPropositionalFormula e1, o, ToPropositionalFormula e2)
        | LtlExpr.LuExpr _
        | LtlExpr.LbExpr _ -> failwith "Unsupported formula operator"
        
    [<RequireQualifiedAccessAttribute>]
    type CuOp =
        | ExistsNext
        | ExistsGlobally
        | ExistsEventually
        | AlwaysNext
        | AlwaysGlobally
        | AlwaysEventually
        
    [<RequireQualifiedAccessAttribute>]
    type CbOp =
        | ExistsUntil
        | AlwaysUntil

    [<RequireQualifiedAccessAttribute>]
    type CtlExpr =
        | Literal of Val
        | ReadField of CompPath * Field
        | ReadFault of CompPath * Fault
        | UExpr of CtlExpr * UOp
        | BExpr of CtlExpr * BOp * CtlExpr
        | CuExpr of CtlExpr * CuOp
        | CbExpr of CtlExpr * CbOp * CtlExpr
        
    // ExtensionModels
    type internal LtlExpr with 
        static member fromPropositionalExpr (propExpr:PropositionalExpr) =
            match propExpr with
                | PropositionalExpr.Literal (_val:Val) ->
                    LtlExpr.Literal(_val) 
                | PropositionalExpr.ReadField (compPath,field:Field) ->
                    LtlExpr.ReadField (compPath,field)
                | PropositionalExpr.ReadFault (compPath,fault:Fault) ->
                    LtlExpr.ReadFault (compPath,fault)
                | PropositionalExpr.UExpr (expr, uop) ->
                    LtlExpr.UExpr (LtlExpr.fromPropositionalExpr expr,uop)
                | PropositionalExpr.BExpr (leftExpr, bop, rightExpr) ->
                    LtlExpr.BExpr (LtlExpr.fromPropositionalExpr leftExpr,bop,LtlExpr.fromPropositionalExpr rightExpr)
        static member createOredExpr (exprs:LtlExpr list) : LtlExpr =
            if exprs.IsEmpty then
                LtlExpr.Literal(Val.BoolVal(false)) //see Conjunctive Normal Form. An empty clause is unsatisfiable
            else if exprs.Tail = [] then
                // only one element, so return it
                exprs.Head
            else
                LtlExpr.BExpr(exprs.Head,BOp.Or,LtlExpr.createOredExpr exprs.Tail)
        static member createAndedExpr (exprs:LtlExpr list) : LtlExpr =
            if exprs.IsEmpty then
                LtlExpr.Literal(Val.BoolVal(true)) //see Conjunctive Normal Form. If there is no clause, the formula is true.
            else if exprs.Tail = [] then
                // only one element, so return it
                exprs.Head
            else
                LtlExpr.BExpr(exprs.Head,BOp.And,LtlExpr.createAndedExpr exprs.Tail)