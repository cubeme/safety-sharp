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
    open SafetySharp.Runtime.Modeling
    open SafetySharp.Reflection
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

    /// Lowers virtual method calls and bindings. Replaces all calls to virtual methods or interface methods with the most derived 
    /// implementation of the target type.
    let rec lowerVirtualCalls (model : Model) (metadataProvider : MetadataProvider) (c : Comp) =
        let replaceVirtualCall componentType methodName t p d r e =
            let declaringType = metadataProvider.GetImplementedType componentType t
            let mutable targetMethod = metadataProvider.UnmapMethod declaringType methodName
            if not targetMethod.IsVirtual then CallExpr (methodName, t, p, d, r, e, false)
            else 
                let targetMethod = Reflection.getMostDerivedMethod componentType targetMethod
                let methodName = metadataProvider.Resolve targetMethod |> Renaming.getUniqueMethodName
                let declaringType = metadataProvider.GetTypeReference(targetMethod.DeclaringType).FullName
                CallExpr (methodName, declaringType, p, d, r, e, false)

        let componentType = model.GetTypeOfComponent c.Name
        let rec lower = function
            | CallExpr (m, t, p, d, r, e, true) -> replaceVirtualCall componentType m t p d r e
            | MemberExpr (Field (f, t), CallExpr (m, dt, p, d, r, e, true)) -> 
                MemberExpr (Field (f, t), replaceVirtualCall (model.GetTypeOfComponent f) m dt p d r e)
            | UExpr (op, e) -> UExpr (op, lower e)
            | BExpr (e1, op, e2) -> BExpr (lower e1, op, lower e2)
            | e -> e

        { c with
            Methods = c.Methods |> List.map (fun m -> { m with Body = Ssm.mapExprsInStm lower m.Body })
            Subs = c.Subs |> List.map (lowerVirtualCalls model metadataProvider) }

    /// Lowers the signatures of ports: Ports returning a value are transformed to void-returning ports 
    /// with an additional out parameter.
    let rec lowerSignatures (c : Comp) =
        let lowerCallSites (m : Method) =
            let rewrite v m t p d r e = CallExpr (m, t, p @ [r], d @ [Out], VoidType, e @ [VarRefExpr v], false)
            let rec lower = function
                | AsgnStm (v, CallExpr (m, t, p, d, r, e, false))                  -> rewrite v m t p d r e |> ExprStm
                | AsgnStm (v, MemberExpr (t, CallExpr (m, dt, p, d, r, e, false))) -> MemberExpr (t, rewrite v m dt p d r e) |> ExprStm
                | AsgnStm (v, TypeExpr (t, CallExpr (m, dt, p, d, r, e, false)))   -> TypeExpr (t, rewrite v m dt p d r e) |> ExprStm
                | SeqStm s          -> SeqStm (s |> List.map lower)
                | IfStm (c, s1, s2) -> IfStm (c, lower s1, lower s2)
                | s                 -> s
            { m with Body = lower m.Body }

        let lowerRetStms retArg (m : Method) =
            let rec lower = function
                | RetStm (Some e)   -> SeqStm [ AsgnStm (retArg, e); RetStm None ]
                | SeqStm s          -> SeqStm (s |> List.map lower)
                | IfStm (c, s1, s2) -> IfStm (c, lower s1, lower s2)
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
    let rec lowerLocalBindings (c : Comp) =
        let synPorts = List<_> ()
        let synBindings = List<_> ()

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
                synBindings.Add { SourceComp = c'.Name; SourcePort = m.Name; TargetComp = c.Name; TargetPort = syn.Name; Kind = BindingKind.Instantaneous }
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
    let rec lowerScheduling (c : Comp) =
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

    /// Inlines all calls to overriden Update methods.
    let rec lowerBaseSteps (c : Comp) = 
        let renameLocal methodName local = sprintf "%s!@!%s" methodName (Ssm.getVarName local)

        let inlineBase baseBody =
            Ssm.mapStms (fun stm ->
                match stm with
                | ExprStm (CallExpr (n, _, _, _, _, _, _)) when c.Methods |> List.exists (fun m -> m.Name = n && m.Kind = Step) -> baseBody
                | _ -> stm
            )

        let renameLocals methodName locals body = 
            locals |> List.fold (fun body local ->
                body |> Ssm.replaceVar local (Local (renameLocal methodName local, Ssm.getVarType local))
            ) body

        let steps = c.Methods |> List.filter (fun m -> m.Kind = Step)
        let step = steps |> List.reduce (fun step m ->
            { step with
                Locals = step.Locals @ (m.Locals |> List.map (fun l -> Local (renameLocal m.Name l, Ssm.getVarType l)))
                Body = m.Body |> renameLocals m.Name m.Locals |> inlineBase step.Body
            }
        ) 
        let step = { step with Body = step.Body |> Ssm.mapStms (fun stm -> match stm with | RetStm _ -> NopStm | _ -> stm) }

        { c with
            Methods = step :: (c.Methods |> List.filter (fun m -> m.Kind <> Step))
            Subs = c.Subs |> List.map lowerBaseSteps
        }

    /// Applies all lowerings to the given components before SSM model validation.
    let lowerPreValidation (model : Model) (root : Comp) : Comp =
        root |> lowerVirtualCalls model (model.GetMetadataProvider ())

    /// Applies all lowerings to the given components after SSM model validation.
    let lowerPostValidation (model : Model) (root : Comp) : Comp =
        root |> lowerSignatures |> lowerLocalBindings |> lowerScheduling |> lowerBaseSteps