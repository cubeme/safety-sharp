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

    /// Lowers the signatures of ports: Ports returning a value are transformed to void-returning ports 
    /// with an additional out parameter.
    let rec lowerSignatures (c : Comp) =
        // Lowers all method call sites:
        // - Statements calls have no return value so there's nothing to do here
        // - Expression calls are always embedded in an assignment statement; we therefore simply add the 
        //   assignment target as the last (out) parameter of the method and convert the assignment into
        //   a statement call
        let lowerCallSites (m : Method) =
            let rec lower = function
                | AsgnStm (v, CallExpr (m, p, d, r, e, t)) -> CallStm (m, p @ [r], d @ [Out], VoidType, e @ [VarRefExpr v], t)
                | SeqStm s                                 -> SeqStm (s |> List.map lower)
                | IfStm (c, s1, s2)                        -> IfStm (c, lower s1, lower s2)
                | s                                        -> s
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

    /// Applies all lowerings to the given components.
    let lower (c : Comp list) : Comp =
        let root = 
            match c with
            | c :: [] -> c
            | c       -> { Name = "SynthesizedRoot"; Subs = c; Fields = []; Methods = []; Faults = []; Bindings = [] }
        
        root |> lowerSignatures //|> removeUnusedLocals