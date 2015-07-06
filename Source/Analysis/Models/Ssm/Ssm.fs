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
open SafetySharp

/// Provides types and functions for working with S# models (SSM). Basically, the S# metamodel is a subset of
/// the metadata and instructions supported by the .NET common language runtime (CLR); a S# model is a view
/// of a .NET assembly.
module internal Ssm =

    /// Represents the unary operators supported by S# models.
    type internal UOp =
        | Minus
        | Not

    /// Represents the binary operators supported by S# models.
    type internal BOp =
        | Add
        | Sub
        | Mul
        | Div
        | Mod
        | And
        | Or
        | Eq
        | Ne
        | Lt
        | Le
        | Gt
        | Ge

    /// Describes the value flow direction of a method parameter.
    type internal ParamDir =
        | In
        | InOut
        | Out

    /// Represents the type of a variable.
    type internal Type = 
        | VoidType
        | BoolType
        | IntType
        | DoubleType
        | ClassType of string

    /// Represents a variable accessed by an expression.
    type internal Var =
        | Arg   of string * Type
        | Local of string * Type
        | Field of string * Type
        | This  of Type

    /// Represents an expression within the body of a S# method.
    type internal Expr = 
        | BoolExpr   of bool
        | IntExpr    of int
        | DoubleExpr of double
        | VarExpr    of Var
        | VarRefExpr of Var
        | UExpr      of UOp * Expr
        | BExpr      of Expr * BOp * Expr
        | MemberExpr of Target : Var * Member : Expr
        | TypeExpr   of Target : string * Member : Expr
        | CallExpr   of Name : string * DeclaringType : string * Params : Type list * ParamDir list * Return : Type * Args : Expr list * IsVirtual : bool

    /// Represents a statement within the body of a S# method.
    type internal Stm =
        | NopStm
        | AsgnStm of Var * Expr
        | SeqStm  of Stm list
        | RetStm  of Expr option
        | ChoiceStm of Expr list * Stm list
        | ExprStm of Expr

    /// Represents a method parameter.
    type internal Param = {
        Var       : Var
        Direction : ParamDir
    }

    /// Indicates whether a method represents a port or a function.
    type internal MethodKind = 
        | ReqPort 
        | ProvPort 
        | Step

    /// Represents a method of a S# component.
    type internal Method = {
        Name   : string
        Params : Param list
        Body   : Stm
        Return : Type
        Locals : Var list
        Kind   : MethodKind
    }

    /// Represents an initial value of a S# field.
    type internal InitVal =
        | BoolVal   of bool
        | IntVal    of int
        | DoubleVal of double

    /// Represents a field of a S# component with zero, one, or more initial values.
    type internal Field = {
        Var  : Var
        Init : InitVal list
    }

    /// Represents a fault of a S# component
    type internal Fault = {
        Name : string
        Methods : Method list
    }

    /// Indicates the kind of a binding.
    type internal BindingKind = 
        | Instantaneous
        | Delayed

    /// Represents a port binding.
    type internal Binding = {
        SourceComp : string
        TargetComp : string
        SourcePort : string
        TargetPort : string
        Kind       : BindingKind
    }

    /// Represents a S# component.
    type internal Comp = {
        Name     : string
        Fields   : Field list
        Methods  : Method list
        Subs     : Comp list
        Faults   : Fault list
        Bindings : Binding list
    }

    let CreateFault name methods =
        { Fault.Name = name; Methods = methods |> Seq.toList }

    let CreateCall name declaringType parameters paramDir returnType args =
        CallExpr (name, declaringType, parameters |> Seq.toList, paramDir |> Seq.toList, returnType, args |> Seq.toList, false)

    let CreateBlock stm =
        stm |> Seq.toList |> SeqStm

    let CreateReturn expr =
        expr |> Option.Some |> RetStm

    let CreateMethod name parameters body returnType locals kind =
        { Name = name; Params = parameters |> Seq.toList; Body = body; Return = returnType; Locals = locals |> Seq.toList; Kind = kind }

    let CreateField name fieldType values = 
        { Var = Field (name, fieldType); Init = values |> Seq.toList }

    let CreateComponent name fields methods subs faults bindings =
        { Name = name; Fields = fields |> Seq.toList; Methods = methods |> Seq.toList; Subs = subs |> Seq.toList; Faults = faults |> Seq.toList; Bindings = bindings |> Seq.toList }

    let CreateChoice guards statements =
        ChoiceStm (guards |> Seq.toList, statements |> Seq.toList)

    /// Gets the type of the given variable.
    let getVarType = function
        | Arg (_, t)   -> t
        | Local (_, t) -> t
        | Field (_, t) -> t
        | This t       -> t

    /// Gets the name of the given variable.
    let getVarName = function
        | Arg (a, _)   -> a
        | Local (l, _) -> l
        | Field (f, _) -> f
        | This _       -> "this"

    /// Gets a value indicating whether the given variable is the implicit 'this' parameter.
    let isThis = function
        | Arg _
        | Local _ 
        | Field _ -> false
        | This _  -> true

    /// Checks whether the variable is of a class type.
    let isClassType v = 
        match getVarType v with
        | ClassType _ -> true
        | _           -> false

    /// Gets the class type of the object variable.
    let getClassType v =
        match getVarType v with
        | ClassType t -> t
        | _           -> invalidOp "The variable is not of a class type."

    /// Gets all variables referenced by the given expression fulfilling the given predicate.
    let rec getVarsOfExpr pred expr =
        match expr with
        | BoolExpr _                     -> []
        | IntExpr _                      -> []
        | DoubleExpr _                   -> []
        | VarExpr v when pred v          -> [v]
        | VarExpr _                      -> []
        | VarRefExpr v when pred v       -> [v]
        | VarRefExpr _                   -> []
        | UExpr (_, e)                   -> getVarsOfExpr pred e
        | BExpr (e1, _, e2)              -> (getVarsOfExpr pred e1) @ (getVarsOfExpr pred e2)
        | CallExpr (_, _, _, _, _, e, _) -> e |> List.map (getVarsOfExpr pred) |> List.collect id
        | MemberExpr (_, m)              -> getVarsOfExpr pred m
        | TypeExpr (_, m)                -> getVarsOfExpr pred m

    /// Gets all local variables referenced by the given expression.
    let rec getLocalsOfExpr = 
        getVarsOfExpr (function Local _ -> true | _ -> false)

    /// Gets all field variables referenced by the given expression.
    let rec getFieldsOfExpr = 
        getVarsOfExpr (function Field _ -> true | _ -> false)

    /// Gets all local variables referenced by the given statement.
    let rec getLocalsOfStm = function
        | NopStm                     -> []
        | AsgnStm (Local (l, t), e)  -> (Local (l, t)) :: getLocalsOfExpr e
        | AsgnStm (v, e)             -> getLocalsOfExpr e
        | SeqStm stms                -> stms |> List.map getLocalsOfStm |> List.collect id
        | RetStm None                -> []
        | RetStm (Some e)            -> getLocalsOfExpr e
        | ChoiceStm (e, s )          -> List.collect getLocalsOfExpr e @ List.collect getLocalsOfStm s
        | ExprStm e                  -> getLocalsOfExpr e

    /// Maps all subexpressions within the given expression using the given map function.
    let rec mapExprs map e =
        match e with
        | UExpr (op, e)                  -> UExpr (op, mapExprs map e) |> map
        | BExpr (e1, op, e2)             -> BExpr (mapExprs map e1, op, mapExprs map e2) |> map
        | MemberExpr (t, e)              -> MemberExpr (t, mapExprs map e) |> map
        | TypeExpr (t, e)                -> TypeExpr (t, mapExprs map e) |> map
        | CallExpr (n, t, p, d, r, a, v) -> CallExpr (n, t, p, d, r, a |> List.map (mapExprs map), v) |> map
        | _                              -> map e

    /// Maps all substatements within the given statement using the given map function.
    let rec mapStms map stm =
        match stm with
        | SeqStm s          -> s |> List.map (mapStms map) |> SeqStm |> map
        | ChoiceStm (e, s)  -> ChoiceStm (e, List.map (mapStms map) s) |> map
        | _                 -> map stm

    /// Maps all expressions within the given statement using the given map function.
    let mapExprsInStm map =
        mapStms (fun stm ->
            match stm with
            | AsgnStm (v, e)    -> AsgnStm (v, map e)
            | RetStm (Some e)   -> RetStm (Some (map e))
            | ChoiceStm (e, s)  -> ChoiceStm (List.map map e, s)
            | ExprStm e         -> ExprStm (map e)
            | _                 -> stm
        )

    /// Replaces the given variable with the given new one.
    let replaceVar oldVar newVar stm =
        stm
        |> mapStms (fun stm ->
            match stm with
            | AsgnStm (v, e) when v = oldVar -> AsgnStm (newVar, e)
            | _                              -> stm
        )
        |> mapExprsInStm (mapExprs (fun e ->
            match e with
            | VarExpr v when v = oldVar         -> VarExpr newVar
            | VarRefExpr v when v = oldVar      -> VarRefExpr newVar
            | MemberExpr (t, e) when t = oldVar -> MemberExpr (newVar, e)
            | _                                 -> e
        ))

    /// Iterates all expressions within the given statement, calling the given function.
    let rec iterExprsInStm func stm =
        match stm with
        | AsgnStm (v, e)    -> func e
        | SeqStm s          -> s |> List.iter (iterExprsInStm func)
        | RetStm (Some e)   -> func e
        | ChoiceStm (e, s)  -> List.iter func e; List.iter (iterExprsInStm func) s
        | ExprStm e         -> func e
        | _                 -> ()