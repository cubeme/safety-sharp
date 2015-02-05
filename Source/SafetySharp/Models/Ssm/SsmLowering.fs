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

/// Lowers SSM models into a normalized form that can be transformed to a SCM model in a trivial way.
module internal SsmLowering =
    open System.Collections.Generic
    open SafetySharp
    open SafetySharp.Modeling
    open Ssm

    /// Makes the given name variable unique within the given method of the given component.
    let private makeUniqueName (c : Comp) (m : Method) name =
        let names = 
            seq { 
                yield! c.Fields |> Seq.map (fun f -> getVarName f.Var)
                yield! m.Locals |> Seq.map getVarName
                yield! m.Params |> Seq.map (fun p -> getVarName p.Var)
            } |> Set.ofSeq

        let mutable name = name
        while names |> Set.contains name do
            name <- name + "_"
        name

    /// Creates a unique synthesized port name based on the given synthesized port index and the given original name.
    let makeSynPortName originalName synIndex =
        sprintf "%s!!%d" originalName synIndex

    /// Gets the given component's subcomponent with the given name.
    let getSub (c : Comp) subName =
        c.Subs |> Seq.filter (fun sub -> sub.Name = subName) |> Seq.exactlyOne

    /// Gets the given component's method with the given name.
    let getMethod (c : Comp) methodName = 
        c.Methods |> Seq.filter (fun m -> m.Name = methodName) |> Seq.exactlyOne

    /// Lowers the signatures of ports: Ports returning a value are transformed to void-returning ports 
    /// with an additional out parameter.
    let rec lowerSignatures (c : Comp) =
        // Lowers all method call sites
        let lowerCallSites (m : Method) =
            let rewrite v m p d r e = CallExpr (m, p @ [r], d @ [Out], VoidType, e @ [VarRefExpr v])
            let rec lower = function
                | AsgnStm (v, CallExpr (m, p, d, r, e))                 -> rewrite v m p d r e |> ExprStm
                | AsgnStm (v, MemberExpr (t, CallExpr (m, p, d, r, e))) -> MemberExpr (t, rewrite v m p d r e) |> ExprStm
                | AsgnStm (v, TypeExpr (t, CallExpr (m, p, d, r, e)))   -> TypeExpr (t, rewrite v m p d r e) |> ExprStm
                | SeqStm s          -> SeqStm (s |> List.map lower)
                | IfStm (c, s1, s2) -> IfStm (c, lower s1, lower s2)
                | s                 -> s
            { m with Body = lower m.Body }

        // Lowers all returns statements of the method:
        // - There's nothing to do for void-returning methods
        // - If a value is returned, the return statement is split into an assignment to the newly introduced out
        //   parameter and a non-value returning return
        let lowerRetStms retArg (m : Method) =
            let rec lower = function
                | RetStm (Some e)   -> SeqStm [ AsgnStm (retArg, e); RetStm None ]
                | SeqStm s          -> SeqStm (s |> List.map lower)
                | IfStm (c, s1, s2) -> IfStm (c, lower s1, lower s2)
                | s                 -> s
            { m with Body = lower m.Body; Return = VoidType }

        // Lowers the signature of the given method.
        let lowerSignature m =
            if m.Return = VoidType then
                lowerCallSites m
            else
                let retArg = Arg (makeUniqueName c m "retVal", m.Return)
                let m = m |> lowerCallSites |> lowerRetStms retArg
                { m with Params = m.Params @ [{ Var = retArg; Direction = Out }] }

        { c with
            Methods = c.Methods |> List.map lowerSignature
            Subs = c.Subs |> List.map lowerSignatures }

    /// Introduces bindings for local provided port invocations. That is, whenever a component invokes a provided port
    /// declared by itself or one of its subcomponents, a required port with matching signature is synthesized and an
    /// instantaneous binding between the provided port and the sythesized required port is added to the component.
    let rec lowerLocalBindings (c : Comp) =
        let synPorts = List<Method> ()
        let synBindings = List<Binding> ()

        let callSynthesized c' n p d r e =
            let m = getMethod c' n
            match m.Kind with
            | ProvPort ->
                let syn = 
                  { m with
                      Name = makeSynPortName m.Name synPorts.Count
                      Kind = ReqPort
                      Body = NopStm 
                      Locals = [] }
                synPorts.Add syn
                synBindings.Add { SourceComp = c'.Name; SourcePort = m.Name; TargetComp = c.Name; TargetPort = syn.Name; Kind = Instantaneous }
                CallExpr (syn.Name, p, d, r, e)
            | _ -> CallExpr (n, p, d, r, e)

        // Lowers all method call sites of provided ports, replacing them with calls to synthesized required ports
        let rec lower = function
            | CallExpr (m, p, d, r, e) -> callSynthesized c m p d r e
            | MemberExpr (Field (f, _), CallExpr (m, p, d, r, e)) -> callSynthesized (getSub c f) m p d r e
            | UExpr (op, e) -> UExpr (op, lower e)
            | BExpr (e1, op, e2) -> BExpr (lower e1, op, lower e2)
            | e -> e

        // Lowers the given method
        let lowerMethod m =
            { m with Body = Ssm.replaceExprs lower m.Body }

        { c with
            Methods = (c.Methods |> List.map lowerMethod) @ (synPorts |> List.ofSeq)
            Subs = c.Subs |> List.map lowerLocalBindings
            Bindings = c.Bindings @ (synBindings |> Seq.toList) }

    /// Applies all lowerings to the given components.
    let lower (root : Comp) : Comp =
        root |> lowerSignatures |> lowerLocalBindings