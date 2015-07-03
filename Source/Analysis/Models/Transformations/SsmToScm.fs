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

/// Transforms lowered SSM models to SCM models.
module internal SsmToScm =
    open SafetySharp
    open SafetySharp.Models

    /// Maps the given SSM type to a SCM type.
    let private mapType (t : Ssm.Type) : Scm.Type =
        match t with
        | Ssm.BoolType   -> Scm.BoolType
        | Ssm.IntType    -> Scm.IntType
        | Ssm.DoubleType -> Scm.RealType
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
        | Ssm.Eq  -> Scm.Equal
        | Ssm.Ne  -> Scm.NotEqual
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
        | Ssm.VarExpr (Ssm.Field (f, _)) -> Scm.Read (Scm.Element.Field( Scm.Field f))
        | Ssm.VarExpr v                  -> Scm.Read (Scm.Element.Var (Scm.Var (Ssm.getVarName v)))
        | Ssm.UExpr (op, e)              -> Scm.UExpr (transformExpr e, mapUOp op)
        | Ssm.BExpr (e1, op, e2)         -> Scm.BExpr (transformExpr e1, mapBOp op, transformExpr e2)
        | _                              -> notSupported "Unsupported SSM expression '%+A'." e

    /// Transforms the given parameter expression of the given direction.
    let private transformParamExpr (e : Ssm.Expr list) (d : Ssm.ParamDir list) : Scm.Param list =
        let transform = function
            | (e, Ssm.In)                                    -> transformExpr e |> Scm.ExprParam 
            | (Ssm.VarRefExpr (Ssm.Local (l, _)), Ssm.InOut) -> Scm.InOutElementParam (Scm.Element.Var (Scm.Var l))
            | (Ssm.VarRefExpr (Ssm.Local (l, _)), Ssm.Out)   -> Scm.InOutElementParam (Scm.Element.Var (Scm.Var l))
            | (Ssm.VarRefExpr (Ssm.Arg (a, _)), Ssm.InOut)   -> Scm.InOutElementParam (Scm.Element.Var (Scm.Var a))
            | (Ssm.VarRefExpr (Ssm.Arg (a, _)), Ssm.Out)     -> Scm.InOutElementParam (Scm.Element.Var (Scm.Var a))
            | (Ssm.VarRefExpr (Ssm.Field (f, _)), Ssm.InOut) -> Scm.InOutElementParam (Scm.Element.Field (Scm.Field f))
            | (Ssm.VarRefExpr (Ssm.Field (f, _)), Ssm.Out)   -> Scm.InOutElementParam (Scm.Element.Field (Scm.Field f))
            | (e, _)                                         -> notSupported "Unsupported inout or out parameter '%+A'." e

        List.zip e d |> List.map transform

    /// Represents SCM 'nop' statement.
    let emptyBlock = Scm.Block []

    /// Transforms the given statement.
    let private transformStm (s : Ssm.Stm) : Scm.Stm =
        let rec transform s = 
            match s with
            | Ssm.NopStm                        -> emptyBlock
            | Ssm.AsgnStm (Ssm.Field (f, _), e) -> Scm.AssignElement (Scm.Element.Field (Scm.Field f), transformExpr e)
            | Ssm.AsgnStm (v, e)                -> Scm.AssignElement (Scm.Element.Var (Scm.Var (Ssm.getVarName v)), transformExpr e)
            | Ssm.SeqStm s                      -> s |> List.map transform |> Scm.Block
            | Ssm.ChoiceStm (e, s)              -> Scm.Choice (List.zip e s |> List.map (fun (e, s) -> transformExpr e, transform s))
            | Ssm.ExprStm (Ssm.MemberExpr (Ssm.Field (f, _), Ssm.CallExpr (m, _, _, d, _, e, false))) -> Scm.StepComp (Scm.Comp f)
            | Ssm.ExprStm (Ssm.CallExpr (m, _, _, d, _, e, false)) -> Scm.CallPort (Scm.ReqPort m, transformParamExpr e d)
            | Ssm.RetStm _ -> emptyBlock
            | _            -> notSupported "Unsupported SSM statement '%+A'." s

        // Removes unnecessary statements
        let rec cleanup = function
            | Scm.Block s ->
                let flattened = s |> Seq.collect (fun s -> match cleanup s with Scm.Block s -> s | s -> [s])
                Scm.Block (flattened |> Seq.toList)
            | s -> s

        s |> transform |> cleanup

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

    /// Transforms the given method to a SCM behavior declaration.
    let private transformBehavior (m : Ssm.Method) : Scm.BehaviorDecl = {
        Locals = m.Locals |> List.map transformLocal
        Body = transformStm m.Body
    }

    /// Transforms the given method to a SCM provided port declaration.
    let private transformProvPort (m : Ssm.Method) : Scm.ProvPortDecl = {
        ProvPort = Scm.ProvPort m.Name
        Params = m.Params |> List.map transformParam 
        FaultExpr = None
        Behavior = transformBehavior m
        Contract = Scm.Contract.None
    }

    /// Transforms the given method to a SCM step declaration.
    let private transformStep (faults : Ssm.Fault list) (m : Ssm.Method) : Scm.StepDecl = {
        FaultExpr = None
        Behavior = 
            let behavior = transformBehavior m
            if faults |> List.isEmpty then
                behavior
            else
                let faultSteps = faults |> List.map (fun fault -> Scm.Fault fault.Name |> Scm.StepFault)
                { behavior with Body = faultSteps @ [behavior.Body] |> Scm.Block }
        Contract = Scm.Contract.None
    }

    /// Transforms the given fault to a SCM fault declaration.
    let private transformFault (f : Ssm.Fault) : Scm.FaultDecl = {
        Fault = Scm.Fault f.Name
        // TODO: Actually transform the occurrence pattern
        Step = { Locals = []
                 Body = Scm.Choice
                      [
                          (Scm.Literal (Scm.BoolVal true), Scm.AssignFault (Scm.Fault f.Name, Scm.Literal (Scm.BoolVal true)))
                          (Scm.Literal (Scm.BoolVal true), Scm.AssignFault (Scm.Fault f.Name, Scm.Literal (Scm.BoolVal false)))
                      ] 
               }
    }

    /// Transforms the provided port fault methods contained in the given fault.
    let private transformFaultProvPorts (f : Ssm.Fault) : Scm.ProvPortDecl list =
        f.Methods
        |> Seq.filter (fun m -> m.Kind = Ssm.ProvPort)
        |> Seq.map transformProvPort
        |> Seq.map (fun p -> { p with FaultExpr = Scm.FaultExpr.Fault (Scm.Fault f.Name) |> Some })
        |> Seq.toList

    /// Transforms the given binding to a SCM binding.
    let private transformBinding (c : Ssm.Comp) (b : Ssm.Binding) : Scm.BndDecl = 
        let getComp (name : string) =
            invalidArg (name.StartsWith c.Name |> not) "name" "Unexpected subcomponent name. Cannot bind port of parent component."
            let lastDot = c.Name.LastIndexOf '.'
            let relativePath = name.Substring (lastDot + 1)
            relativePath.Split '.' |> Array.filter ((<>) "") |> Array.rev |> Array.map Scm.Comp |> Array.toList

        { Target = { ReqPort = Scm.ReqPort b.TargetPort; Comp = getComp b.TargetComp }
          Source = { ProvPort = Scm.ProvPort b.SourcePort; Comp = getComp b.SourceComp }
          Kind = match b.Kind with 
                 | Ssm.Instantaneous -> Scm.Instantaneous 
                 | Ssm.Delayed       -> Scm.Delayed }

    /// Transforms the given (lowered) SSM model to a SCM model.
    let rec transform (c : Ssm.Comp) : Scm.CompDecl = {
        Comp = Scm.Comp (c.Name.Substring (c.Name.LastIndexOf '.' + 1))
        Subs = c.Subs |> List.map transform
        Fields = c.Fields |> List.map transformField
        Faults = c.Faults |> List.map transformFault 
        // TODO: Support fault injections in required ports
        ReqPorts = c.Methods |> Seq.filter (fun m -> m.Kind = Ssm.ReqPort) |> Seq.map transformReqPort |> Seq.toList
        ProvPorts = 
            let noFaults = c.Methods |> Seq.filter (fun m -> m.Kind = Ssm.ProvPort) |> Seq.map transformProvPort |> Seq.toList
            let faults = c.Faults |> List.collect transformFaultProvPorts
            noFaults @ faults
        Bindings = c.Bindings |> List.map (transformBinding c)
        // TODO: Support fault injections in step methods
        Steps = c.Methods |> Seq.filter (fun m -> m.Kind = Ssm.Step) |> Seq.map (transformStep c.Faults) |> Seq.toList
    }
        