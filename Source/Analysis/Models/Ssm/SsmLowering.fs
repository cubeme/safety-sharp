﻿// The MIT License (MIT)
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
module SsmLowering =
    open System.Collections.Generic
    open SafetySharp
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
    let private makeSynPortName originalName synIndex =
        sprintf "%s@%d" originalName synIndex

    /// Gets the given component's subcomponent with the given name.
    let private getSub (c : Comp) subName =
        c.Subs |> Seq.filter (fun sub -> sub.Name.EndsWith(sprintf ".%s" subName)) |> Seq.exactlyOne

    /// Gets the given component's method with the given name.
    let private getMethod (c : Comp) methodName = 
        c.Methods |> Seq.filter (fun m -> m.Name = methodName) |> Seq.exactlyOne

    /// Lowers the signatures of ports: Ports returning a value are transformed to void-returning ports 
    /// with an additional out parameter.
    let rec private lowerSignatures (c : Comp) =
        let lowerCallSites (m : Method) =
            let rewrite v m t p d r e = CallExpr (m, t, p @ [r], d @ [Out], VoidType, e @ [VarRefExpr v], false)
            let rec lower = function
                | AsgnStm (v, CallExpr (m, t, p, d, r, e, false))                  -> rewrite v m t p d r e |> ExprStm
                | AsgnStm (v, MemberExpr (t, CallExpr (m, dt, p, d, r, e, false))) -> MemberExpr (t, rewrite v m dt p d r e) |> ExprStm
                | AsgnStm (v, TypeExpr (t, CallExpr (m, dt, p, d, r, e, false)))   -> TypeExpr (t, rewrite v m dt p d r e) |> ExprStm
                | SeqStm s          -> SeqStm (s |> List.map lower)
                | ChoiceStm (c, s)  -> ChoiceStm (c, List.map lower s)
                | s                 -> s
            { m with Body = lower m.Body }

        let lowerRetStms retArg (m : Method) =
            let rec lower = function
                | RetStm (Some e)   -> SeqStm [ AsgnStm (retArg, e); RetStm None ]
                | SeqStm s          -> SeqStm (s |> List.map lower)
                | ChoiceStm (c, s)  -> ChoiceStm (c, List.map lower s)
                | s                 -> s
            { m with Body = lower m.Body; Return = VoidType }

        let lowerSignature m =
            if m.Return = VoidType then
                lowerCallSites m
            else
                let retArg = Arg (makeUniqueName c m "retVal", m.Return)
                let m = m |> lowerCallSites |> lowerRetStms retArg
                { m with Params = m.Params @ [{ Var = retArg; Direction = Out }] }

        { c with
            Methods = c.Methods |> List.map lowerSignature
            Faults = c.Faults |> List.map (fun f -> { f with Methods = f.Methods |> List.map lowerSignature })
            Subs = c.Subs |> List.map lowerSignatures }

    /// Introduces bindings for local provided port invocations. That is, whenever a component invokes a provided port
    /// declared by itself or one of its subcomponents, a required port with matching signature is synthesized and an
    /// instantaneous binding between the provided port and the sythesized required port is added to the component.
    let rec private lowerLocalBindings (c : Comp) =
        let synPorts = List<_> ()
        let synBindings = List<_> ()

        let name c' =
            c'.Name

        let callSynthesized c' (m : Method) t p d r e =
            match m.Kind with
            | ProvPort ->
                let syn = 
                  { m with
                      Name = makeSynPortName m.Name synPorts.Count
                      Kind = ReqPort
                      Body = NopStm 
                      Locals = [] }
                synPorts.Add syn
                synBindings.Add { SourceComp = name c'; SourcePort = m.Name; TargetComp = name c; TargetPort = syn.Name; Kind = BindingKind.Instantaneous }
                CallExpr (syn.Name, t, p, d, r, e, false)
            | _ -> CallExpr (m.Name, t, p, d, r, e, false)

        let rec lower expr = 
            match expr with
            | CallExpr (m, t, p, d, r, e, false) -> callSynthesized c (getMethod c m) t p d r e
            | MemberExpr (Field (f, _), CallExpr (m, t, p, d, r, e, false)) -> 
                let c = getSub c f
                let m = getMethod c m
                match m.Kind with
                | ProvPort -> callSynthesized c m t p d r e
                | ReqPort  -> notSupported "Cannot invoke required port of subcomponent."
                | Step     -> expr
            | UExpr (op, e) -> UExpr (op, lower e)
            | BExpr (e1, op, e2) -> BExpr (lower e1, op, lower e2)
            | _ -> expr

        { c with
            Methods = (c.Methods |> List.map (fun m -> { m with Body = Ssm.mapExprsInStm lower m.Body })) @ (synPorts |> List.ofSeq)
            Subs = c.Subs |> List.map lowerLocalBindings
            Bindings = c.Bindings @ (synBindings |> Seq.toList) }

    /// Introduces calls to the component's subcomponents' Update methods in accordance with the component's scheduling metadata.
    let rec private lowerScheduling (c : Comp) =
        let lower (m : Method) =
            match m.Kind with
            | Step when c.Subs <> [] ->
                let stepCalls = 
                    c.Subs // TODO: Respect scheduling metadata
                    |> List.map (fun sub ->
                        // Note: We don't know the original type of the subcomponent at this point, but we don't really care about it anyway...
                        let name = 
                            let lastDot = sub.Name.LastIndexOf "."
                            if lastDot = -1 then sub.Name else sub.Name.Substring (lastDot + 1)
                        ExprStm (MemberExpr (Field (name, ClassType ""), CallExpr ("Update", "", [], [], VoidType, [], false)))
                    )

                let body = SeqStm (stepCalls @ [m.Body])
                { m with Body = body }
            | _ -> m

        { c with
            Methods = c.Methods |> List.map lower
            Subs = c.Subs |> List.map lowerScheduling }

    /// Applies all lowerings to the given components after SSM model validation.
    let Lower (root : Comp) : Comp =
        root |> lowerSignatures |> lowerLocalBindings |> lowerScheduling