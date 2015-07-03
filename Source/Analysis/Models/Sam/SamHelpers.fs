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
open SafetySharp.Models.Sam

module internal SamHelpers =


    // Extension methods
    type Var with
        member var.getName =
            match var with
                | Var (name) -> name


    // Extension methods
    type Element with
        member elem.getName =
            match elem with
                | Element.GlobalVar (var) -> var.getName
                | Element.LocalVar (var) -> var.getName
                 
    // Extension methods
    type Expr with
        static member createOredExpr (exprs:Expr list) : Expr =
            if exprs.IsEmpty then
                Expr.Literal(Val.BoolVal(false)) //see Conjunctive Normal Form. An empty clause is unsatisfiable
            else if exprs.Tail = [] then
                // only one element, so return it
                exprs.Head
            else
                Expr.BExpr(exprs.Head,BOp.Or,Expr.createOredExpr exprs.Tail)
        static member createAndedExpr (exprs:Expr list) : Expr =
            if exprs.IsEmpty then
                Expr.Literal(Val.BoolVal(true)) //see Conjunctive Normal Form. If there is no clause, the formula is true.
            else if exprs.Tail = [] then
                // only one element, so return it
                exprs.Head
            else
                Expr.BExpr(exprs.Head,BOp.And,Expr.createAndedExpr exprs.Tail)        
        
    // Extension methods
    type LocalVarDecl with
        static member createLocalVarDecl (_var:Var) (_type:Type) : LocalVarDecl=
            {
                LocalVarDecl.Var = _var
                LocalVarDecl.Type = _type;
            }
            
    // Extension methods
    type Pgm with
        member this.getTraceables : Traceable list  =
            this.Globals |> List.map (fun gl -> Traceable(gl.Var))

        (*
        member expr.getSamType (varToType:Map<Var,Type>) : Type =
            // TODO: things like a==b==c not supported yet
            // TODO: rewrite to be more efficient
            match expr with
                | Expr.Literal (_val) ->
                    match _val with
                        | SafetySharp.Models.Sam.BoolVal (_) -> Type.BoolType
                        | SafetySharp.Models.Sam.NumbVal (_) -> Type.IntType
                | Expr.Read (_var) ->
                    varToType.Item _var
                | Expr.ReadOld (_var) ->
                    varToType.Item _var
                | Expr.UExpr (expr,uop) ->
                    // TODO: Check, if uop matches to type
                    expr.getSamType varToType
                | Expr.BExpr (left, bop, right) ->
                    let leftType = left.getSamType varToType //very inefficient, if this has to be done
                    let rightType = right.getSamType varToType //very inefficient, if this has to be done
                    let leftIntRightIntOutBool () =                        
                        if leftType = Type.IntType && rightType = Type.IntType then Type.BoolType else failwith "types don't match"
                    let leftBoolRightBoolOutBool () =
                        if leftType = Type.IntType && rightType = Type.IntType then Type.BoolType else failwith "types don't match"
                    let leftTypeEqualsRightTypeOutBool () =                        
                        if leftType = rightType then Type.BoolType else failwith "types don't match"
                    match bop with
                        | BOp.Add -> leftIntRightIntOutBool ()
                        | BOp.Subtract -> leftIntRightIntOutBool ()
                        | BOp.Multiply -> leftIntRightIntOutBool ()
                        | BOp.Divide -> leftIntRightIntOutBool ()
                        | BOp.Modulo -> leftIntRightIntOutBool ()
                        | BOp.And -> leftBoolRightBoolOutBool ()
                        | BOp.Or -> leftBoolRightBoolOutBool ()
                        | BOp.Implies -> leftBoolRightBoolOutBool ()
                        | BOp.Equals -> leftTypeEqualsRightTypeOutBool ()
                        | BOp.NotEquals -> leftTypeEqualsRightTypeOutBool ()
                        | BOp.Less -> leftIntRightIntOutBool ()
                        | BOp.LessEqual -> leftIntRightIntOutBool ()
                        | BOp.Greater -> leftIntRightIntOutBool ()
                        | BOp.GreaterEqual -> leftIntRightIntOutBool ()
        *)