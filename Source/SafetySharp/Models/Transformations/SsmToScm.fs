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

namespace SafetySharp.Models.Transformations

/// Transforms lowered SSM models to SCM models.
module internal SsmToScm =
    open SafetySharp
    open SafetySharp.Models

    /// Maps the given SSM type to a SCM type.
    let private mapType (t : Ssm.Type) : Scm.Type =
        match t with
        | Ssm.BoolType   -> Scm.BoolType
        | Ssm.IntType    -> Scm.IntType
        | Ssm.DoubleType -> notImplemented ()
        | _              -> invalidOp "Invalid type '%+A'." t

    /// Maps the given SSM initial field value to a SCM literal
    let private mapInitVal (v : Ssm.InitVal) : Scm.Val =
        match v with
        | Ssm.BoolVal b   -> Scm.BoolVal b
        | Ssm.IntVal i    -> Scm.IntVal i
        | Ssm.DoubleVal d -> notImplemented ()

    /// Maps the given SSM parameter direction to a SCM direction.
    let private mapDirection (d : Ssm.ParamDir) : Scm.ParamDir =
        match d with
        | Ssm.In    -> Scm.In
        | Ssm.InOut
        | Ssm.Out   -> Scm.InOut

    /// Maps the given SSM unary operator to a SCM unary operator.
    let private mapUOp (op : Ssm.UOp) : Scm.UOp =
        match op with
        | Ssm.Minus -> Scm.Minus
        | Ssm.Not   -> Scm.Not

    /// Maps the given SSM binary operator to a SCM binary operator.
    let private mapBOp (op : Ssm.BOp) : Scm.BOp =
        match op with
        | Ssm.Add -> Scm.Add
        | Ssm.Sub -> Scm.Subtract
        | Ssm.Mul -> Scm.Multiply
        | Ssm.Div -> Scm.Divide
        | Ssm.Mod -> Scm.Modulo
        | Ssm.And -> Scm.And
        | Ssm.Or  -> Scm.Or
        | Ssm.Eq  -> Scm.Equals
        | Ssm.Ne  -> Scm.NotEquals
        | Ssm.Lt  -> Scm.Less
        | Ssm.Le  -> Scm.LessEqual
        | Ssm.Gt  -> Scm.Greater
        | Ssm.Ge  -> Scm.GreaterEqual

    /// Transforms the given expression.
    let rec private transformExpr (e : Ssm.Expr) : Scm.Expr =
        match e with
        | Ssm.BoolExpr b                 -> Scm.Literal (Scm.BoolVal b)
        | Ssm.IntExpr i                  -> Scm.Literal (Scm.IntVal i)
        | Ssm.DoubleExpr d               -> notImplemented ()
        | Ssm.VarExpr (Ssm.Field (f, _)) -> Scm.ReadField (Scm.Field f)
        | Ssm.VarExpr v                  -> Scm.ReadVar (Scm.Var (Ssm.getVarName v))
        | Ssm.UExpr (op, e)              -> Scm.UExpr (transformExpr e, mapUOp op)
        | Ssm.BExpr (e1, op, e2)         -> Scm.BExpr (transformExpr e1, mapBOp op, transformExpr e2)
        | _                              -> notSupported "Unsupported SSM expression '%+A'." e

    /// Transforms the given statement.
    let rec private transformStm (s : Ssm.Stm) : Scm.Stm =
        match s with
        | Ssm.NopStm                        -> Scm.Block [] 
        | Ssm.AsgnStm (Ssm.Field (f, _), e) -> Scm.AssignField (Scm.Field f, transformExpr e)
        | Ssm.AsgnStm (v, e)                -> Scm.AssignVar (Scm.Var (Ssm.getVarName v), transformExpr e)
        | Ssm.SeqStm s                      -> s |> List.map transformStm |> Scm.Block
        | Ssm.IfStm (e, s1, Some s2)        -> 
            let e = transformExpr e
            Scm.Choice [(e, transformStm s1); (Scm.UExpr (e, Scm.Not), transformStm s2)]
        | Ssm.CallStm (m, p, d, r, e, t)    -> 
            Scm.CallPort (Scm.ReqPort m.Name, []) // TODO
        | Ssm.RetStm _                      -> Scm.Block [] // TODO: Remove
        | _                                 -> notSupported "Unsupported SSM statement '%+A'." s

    /// Transforms the given local variable.
    let private transformLocal (l : Ssm.Var) : Scm.VarDecl =
        match l with
        | Ssm.Local (l, t) -> { Var = Scm.Var l; Type = mapType t }
        | _                -> invalidOp "Expected a local variable."

    /// Transforms the given field variable.
    let private transformField (f : Ssm.Field) : Scm.FieldDecl =
        match f.Var with
        | Ssm.Field (n, t) -> { Field = Scm.Field n; Type = mapType t; Init = f.Init |> List.map mapInitVal }
        | _                -> invalidOp "Expected a field variable."

    /// Transforms the given method parameter.
    let private transformParam (p : Ssm.Param) : Scm.ParamDecl =
        match p.Var with
        | Ssm.Arg (a, t) -> { Var = { Var = Scm.Var a; Type = mapType t }; Dir = mapDirection p.Direction }
        | _              -> invalidOp "Expected an argument."

    /// Transforms the given method to a SCM required port declaration.
    let private transformReqPort (m : Ssm.Method) : Scm.ReqPortDecl = {
        ReqPort = Scm.ReqPort m.Name
        Params = m.Params |> List.map transformParam
    }

    /// Transforms the given method to a SCM provided port declaration.
    let private transformProvPort (m : Ssm.Method) : Scm.ProvPortDecl = {
        ProvPort = Scm.ProvPort m.Name
        Params = m.Params |> List.map transformParam 
        FaultExpr = None
        Behavior = 
        { 
            Locals = m.Locals |> List.map transformLocal
            Body = transformStm m.Body
        }
    }

    /// Transforms the given (lowered) SSM model to a SCM model.
    let rec transform (c : Ssm.Comp) : Scm.CompDecl = {
        Comp = Scm.Comp c.Name
        Subs = c.Subs |> List.map transform
        Fields = c.Fields |> List.map transformField
        Faults = []
        ReqPorts = c.Methods |> Seq.filter (fun m -> m.Kind = Ssm.ReqPort) |> Seq.map transformReqPort |> Seq.toList
        ProvPorts = c.Methods |> Seq.filter (fun m -> m.Kind = Ssm.ProvPort) |> Seq.map transformProvPort |> Seq.toList
        Bindings = []
        Steps = []
    }
        