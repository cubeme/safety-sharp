// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software type associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, type/or sell
// copies of the Software, type to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice type this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE type NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

module Test

type Var = Var of string
type Field = Field of string
type ReqPort = ReqPort of string
type ProvPort = ProvPort of string
type Comp = Comp of string

type UOp =
    | Minus
    | Not

type BOp =
    | Add
    | Subtract
    | Multiply
    | Divide
    | Modulo
    | And
    | Or
    | Equals
    | NotEquals
    | Less
    | LessEqual
    | Greater
    | GreaterEqual

type Val = 
    | BoolVal of bool
    | IntVal of int

type Expr =
    | Literal of Val
    | ReadVar of Var
    | ReadField of Field
    | UExpr of Expr * UOp
    | BExpr of Expr * BOp * Expr

type Stm =
    | Skip
    | AssignVar of Var * Expr
    | AssignField of Field * Expr
    | Block of Stm list
    | GrdCmd of (Expr * Stm) list
    | CallPort of ReqPort * Expr list * Var list
    | CallComp of Comp

type Type =
    | BoolType
    | IntType

type FieldSym = {
    Field : Field
    Type : Type
    Init : Val list 
}

type VarSym = {
    Var : Var
    Type : Type
}

type ReqPortSym = {
    ReqPort : ReqPort
    InParams : Type list
    InOutParams : Type list
}

type ProvPortSym = {
    ProvPort : ProvPort
    InParams : VarSym list
    InOutParams : VarSym list
    Locals : VarSym list
    Stm : Stm
}

type BindingType = Instantaneous | Delayed

type BindingSym = {
    ReqPort : ReqPort
    ProvPort : ProvPort
    ReqComp : Comp
    ProvComp : Comp
    Type : BindingType
}

type CompSym = {
    Comp : Comp
    Subcomp : CompSym list
    Fields : FieldSym list
    ReqPorts : ReqPortSym list
    ProvPorts : ProvPortSym list
    Bindings : BindingSym list
    Locals : VarSym list
    Stm : Stm
}