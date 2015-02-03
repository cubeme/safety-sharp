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
open SafetySharp.Modeling

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
        | ClassType  of string

    /// Represents a variable accessed by an expression.
    type internal Var =
        | Arg   of string * Type
        | Local of string * Type
        | Field of string * Type
        | This  of Type

    /// Uniquely identifies a method.
    type internal MethodId = {
        Type : string
        Name : string
    }

    /// Represents an expression within the body of a S# method.
    type internal Expr = 
        | BoolExpr   of bool
        | IntExpr    of int
        | DoubleExpr of double
        | VarExpr    of Var
        | VarRefExpr of Var
        | UExpr      of UOp * Expr
        | BExpr      of Expr * BOp * Expr
        | CallExpr   of MethodId * Params : Type list * ParamDir list * Return : Type * Args : Expr list * Target : Expr option

    /// Represents a statement within the body of a S# method.
    type internal Stm =
        | NopStm
        | AsgnStm of Var * Expr
        | GotoStm of Expr * int
        | SeqStm  of Stm list
        | RetStm  of Expr option
        | IfStm   of Expr * Stm * Stm
        | CallStm of MethodId * Params : Type list * ParamDir list * Return : Type * Args : Expr list * Target : Expr option

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
        // TODO   
    }

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

    /// Gets the set of statement program counters that can be executed following the execution of the
    /// statement at the given program counter. For non-branching statements, the successor is always
    /// the next statement of the method's body. Branching statements, on the other hand, typically
    /// have more than one successor. Return statements don't have any successor at all.
    let private getSuccessors methodBody pc =
        let succs = function
            | GotoStm (BoolExpr true, pc') -> Set.singleton pc'
            | GotoStm (_, pc') -> [pc'; pc + 1] |> Set.ofList
            | RetStm _ -> Set.empty
            | _ -> pc + 1 |> Set.singleton

        // Get the successors of the statement at the given program counter, removing 
        // the 'method end' program counter from the resulting set
        pc
        |> Array.get methodBody
        |> succs
        |> Set.remove (methodBody.Length)

    /// Gets the control flow graph, mapping each statement (identified by its program counter) to the set
    /// of program counters of its successor statements.
    let private getCfg methodBody =
        let addToSet map k v =
            match Map.tryFind k map with
            | Some v' -> map |> Map.add k (Set.union v v')
            | None    -> map |> Map.add k v

        methodBody 
        |> Array.fold (fun (succs, pc) instr ->
            (addToSet succs pc <| getSuccessors methodBody pc, pc + 1)
        ) (Map.empty, 0)
        |> fst

    /// Gets the set of all paths starting at the given statement (identified by its program counter) to the
    /// end of the method body.
    let rec private getPaths cfg pc =
        match Map.find pc cfg |> List.ofSeq with
        | [] -> [[pc]]
        | succs -> 
            succs 
            |> List.map (fun pc' -> getPaths cfg pc') 
            |> List.collect id
            |> List.map (fun pc' -> pc :: pc')

    /// Gets the join point for the given statement (identified by its program counter). The join point is the
    /// first statement that is executed on all paths starting at the given statement. A value of 'None' is returned
    /// if the paths do not converge before the method returns.
    let private getJoinPoint cfg pc =
        let common = Set.intersectMany (getPaths cfg pc |> List.map Set.ofList)
        let common = Set.difference common (Set.singleton pc)
        if Set.isEmpty common then None
        else Set.minElement common |> Some

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

    /// Deduces the type of the expression.
    let rec deduceType expr =
        let deduceResultingNonBoolType e1 e2 =
            match (deduceType e1, deduceType e2) with
            | (IntType, IntType)       -> IntType
            | (DoubleType, IntType)    -> DoubleType
            | (IntType, DoubleType)    -> DoubleType
            | (DoubleType, DoubleType) -> DoubleType
            | _                        -> invalidOp "Type deduction failure."

        let bothAreBool e1 e2 =
            match (deduceType e1, deduceType e2) with
            | (BoolType, BoolType) -> true
            | _                    -> false

        let bothAreNonBool e1 e2 =
            match (deduceType e1, deduceType e2) with
            | (BoolType, _) -> false
            | (_, BoolType) -> false
            | _             -> true

        match expr with
        | BoolExpr _ -> BoolType
        | IntExpr _ -> IntType
        | DoubleExpr _ -> DoubleType
        | VarExpr v -> getVarType v
        | VarRefExpr v -> getVarType v
        | UExpr (Minus, e) when deduceType e = IntType -> IntType
        | UExpr (Minus, e) when deduceType e = DoubleType -> DoubleType
        | UExpr (Not, e) when deduceType e = BoolType -> BoolType
        | BExpr (e1, Add, e2) -> deduceResultingNonBoolType e1 e2
        | BExpr (e1, Sub, e2) -> deduceResultingNonBoolType e1 e2
        | BExpr (e1, Mul, e2) -> deduceResultingNonBoolType e1 e2
        | BExpr (e1, Div, e2) -> deduceResultingNonBoolType e1 e2
        | BExpr (e1, Mod, e2) -> deduceResultingNonBoolType e1 e2
        | BExpr (e1, And, e2) when bothAreBool e1 e2 -> BoolType
        | BExpr (e1, Or, e2) when bothAreBool e1 e2 -> BoolType
        | BExpr (e1, Eq, e2) when bothAreBool e1 e2 || bothAreNonBool e1 e2 -> BoolType
        | BExpr (e1, Ne, e2) when bothAreBool e1 e2 || bothAreNonBool e1 e2 -> BoolType
        | BExpr (e1, Lt, e2) when bothAreNonBool e1 e2 -> BoolType
        | BExpr (e1, Le, e2) when bothAreNonBool e1 e2 -> BoolType
        | BExpr (e1, Gt, e2) when bothAreNonBool e1 e2 -> BoolType
        | BExpr (e1, Ge, e2) when bothAreNonBool e1 e2 -> BoolType
        | CallExpr (_, _, _, t, _, _) -> t
        | _ -> invalidOp "Type deduction failure."

    /// Gets all variables referenced by the given expression fulfilling the given predicate.
    let rec getVarsOfExpr pred expr =
        match expr with
        | BoolExpr _                  -> []
        | IntExpr _                   -> []
        | DoubleExpr _                -> []
        | VarExpr v when pred v       -> [v]
        | VarExpr _                   -> []
        | VarRefExpr v when pred v    -> [v]
        | VarRefExpr _                -> []
        | UExpr (_, e)                -> getVarsOfExpr pred e
        | BExpr (e1, _, e2)           -> (getVarsOfExpr pred e1) @ (getVarsOfExpr pred e2)
        | CallExpr (_, _, _, _, e, _) -> e |> List.map (getVarsOfExpr pred) |> List.collect id

    /// Gets all local variables referenced by the given expression.
    let rec getLocalsOfExpr = 
        getVarsOfExpr (function Local (l, t) -> true | _ -> false)

    /// Gets all field variables referenced by the given expression.
    let rec getFieldsOfExpr = 
        getVarsOfExpr (function Field (f, t) -> true | _ -> false)

    /// Gets all local variables referenced by the given statement.
    let rec getLocalsOfStm = function
        | NopStm                     -> []
        | AsgnStm (Local (l, t), e)  -> (Local (l, t)) :: getLocalsOfExpr e
        | AsgnStm (v, e)             -> getLocalsOfExpr e
        | GotoStm (e, t)             -> getLocalsOfExpr e
        | SeqStm stms                -> stms |> List.map getLocalsOfStm |> List.collect id
        | RetStm None                -> []
        | RetStm (Some e)            -> getLocalsOfExpr e
        | IfStm (e, s1, s2)          -> (getLocalsOfExpr e) @ (getLocalsOfStm s1) @ (getLocalsOfStm s2)
        | CallStm (_, _, _, _, e, _) -> e |> List.map getLocalsOfExpr |> List.collect id

    /// Replaces all goto statements in the given method body with structured control flow statements.
    /// If a goto cannot be removed, the method body is invalid.
    let replaceGotos methodBody =
        let cfg = getCfg methodBody

        let append stm stm' =
            match stm' with
            | NopStm      -> stm
            | SeqStm stm' -> SeqStm (stm :: stm')
            | stm'        -> SeqStm [stm; stm']

        // Transforms all statements in the range [pc, last-1]
        let rec transform pc last =
            let getJoinPoint () =
                let joinPoint = getJoinPoint cfg pc
                match joinPoint with 
                    | None -> last 
                    | Some j -> j

            if pc >= last then NopStm
            else
                match Array.get methodBody pc with
                | GotoStm (BoolExpr true, t) when t = last ->
                    NopStm
                | GotoStm (BoolExpr true, t) ->
                    let joinPoint = getJoinPoint ()
                    let thenStm = transform t joinPoint
                    let elseStm = NopStm
                    let ifStm = IfStm (BoolExpr true, thenStm, elseStm)
                    let joinedStm = transform joinPoint last
                    append ifStm joinedStm
                | GotoStm (e, t) ->
                    let joinPoint = getJoinPoint ()
                    // There might be no then-stm if the goto represents an 'if' without an 'else'
                    // (note that the C# compiler inverts the condition and switches the original then and else statements)
                    let thenStm = if cfg.[pc] |> Set.contains joinPoint then NopStm else transform t joinPoint
                    let elseStm = transform (pc + 1) joinPoint
                    let ifStm = IfStm (e, thenStm, elseStm)
                    let joinedStm = transform joinPoint last
                    append ifStm joinedStm
                | RetStm e -> RetStm e
                | stm -> append stm (transform (pc + 1) last)

        let last = Array.length methodBody
        transform 0 last