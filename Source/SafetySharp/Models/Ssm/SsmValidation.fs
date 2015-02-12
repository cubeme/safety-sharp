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

open System
open System.Collections.Generic
open System.Reflection
open SafetySharp
open SafetySharp.Modeling
open Ssm
open QuickGraph
open QuickGraph.Algorithms

/// Raised when one or more invalid port bindings were encountered that involve a port of a component that is not
/// part of the declaring component's sub tree.
type InvalidBindingsException internal (invalidBindings : PortBinding array) =
    inherit Exception (
        let bindings = String.Join ("\n", invalidBindings |> Array.map (fun binding ->
            sprintf "Component '%s', Port '%A' = Component '%s', Port '%A' [%A]; binding established by Component '%s'"
                (binding.TargetPort.Component :?> Component).UnmangledName binding.TargetPort.Method
                (binding.SourcePort.Component :?> Component).UnmangledName binding.SourcePort.Method
                binding.Kind binding.BinderName
        ))
        sprintf "One or more bindings are invalid because they involve a port of a component that is not part of the declaring component's sub tree:\n%s\n\
                 Check the 'InvalidBindings' property of this exception instance for further details about the invalid bindings." bindings)

    /// Gets the invalid port bindings the exception was raised for.
    member this.InvalidBindings = invalidBindings

/// Raised when one or more unbound required ports were found.
type UnboundRequiredPortsException internal (unboundPorts : PortInfo array) =
    inherit Exception (
        let ports = String.Join ("\n", unboundPorts |> Array.map (fun p -> 
            sprintf "Component '%s', Port '%A'" (p.Component :?> Component).UnmangledName p.Method))
        sprintf "One or more unbound required ports detected:\n%s\nCheck the 'UnboundPorts' property of this exception instance for further \
                 details about the unbound ports." ports)

    /// Gets the unbound required ports the exception was raised for.
    member this.UnboundPorts = unboundPorts

/// Raised when one or more required ports have more than one binding.
type AmbiguousRequiredPortBindingsException internal (ambiguousBindings : PortBinding array array) =
    inherit Exception (
        let bindings = String.Join ("\n", ambiguousBindings |> Array.map (fun bindings ->
            let ambiguousBindings = String.Join ("\n     ", bindings |> Array.map (fun binding -> 
                sprintf "bound to: Component '%s', Port '%A' [%A]; binding established by Component '%s'" 
                    (binding.SourcePort.Component :?> Component).UnmangledName binding.SourcePort.Method binding.Kind binding.BinderName
            ))
            sprintf "Component '%s', Port '%A':\n     %s" 
                (bindings.[0].TargetPort.Component :?> Component).UnmangledName bindings.[0].TargetPort.Method ambiguousBindings
        ))
        sprintf "Detected an ambiguous binding for one or more required ports:\n%s\nCheck the 'AmbiguousBindings' property of this exception instance \
                 for further details about the ambiguous port bindings." bindings)

    /// Gets the unbound required ports the exception was raised for.
    member this.AmbiguousBindings = ambiguousBindings

/// Raised when a cycle in the control flow of a model exists.
type CyclicControlFlowException internal (cycle : (Component * MethodInfo) array) =
    inherit Exception (
        let print (c : Component, m : MethodInfo) = sprintf "Component '%s', Method '%A'" c.UnmangledName m
        let info = String.Join ("\n   ", cycle |> Array.map print)
        sprintf "A cycle has been detected in the control flow of the model. Recursion is not allowed or must be broken up by a delayed binding. \
                 Involved methods:\n\n   %s\n   %s\n   ...\n\nCheck the 'ControlFlow' property of this exception instance \
                 for further details about the methods and objects that constitute the cycle." info (print cycle.[0]))

    /// Gets the methods and objects constituting the cycle.
    member this.ControlFlow = cycle

/// Performs a couple of validation checks on a lowered SSM model.
module internal SsmValidation =
    
    /// Maps the given information to a <see cref="PortInfo" /> instance.
    let private toPortInfo (model : Model) (componentName : string) (portName : string) = 
        let c = model.FindComponent componentName
        PortInfo (c, model.MetadataProvider.UnmapMethod (c.GetType ()) portName)

    /// Maps the given information to a <see cref="PortBinding" /> instance.
    let private toPortBinding (model : Model) (componentName : string) (binding : Binding) =
        let portBinding = PortBinding (toPortInfo model binding.TargetComp binding.TargetPort, toPortInfo model binding.SourceComp binding.SourcePort)
        portBinding.Kind <- binding.Kind
        portBinding.Binder <- model.FindComponent componentName
        portBinding

    /// Selects all elements from the given component hierarchy using the given selector function.
    let rec private collect selector (c : Comp) = seq {
        yield! selector c |> Seq.map (fun e -> (c, e))
        yield! c.Subs |> Seq.collect (collect selector)
    }

    /// Checks for invalid bindings, i.e., bindings involving a port of a component that is not part of the declaring component's sub tree.
    let private invalidBindings (model : Model) (c : Comp) =
        let rec check (c : Comp) = seq {
            let invalidComp (portComponent : string) = portComponent.StartsWith c.Name |> not
            yield! c.Bindings 
                   |> Seq.filter (fun binding -> invalidComp binding.SourceComp || invalidComp binding.TargetComp) 
                   |> Seq.map (fun binding -> (c, binding))
            yield! c.Subs |> Seq.map check |> Seq.collect id
        }

        let bindings = check c |> Seq.toArray
        if bindings.Length > 0 then
            raise (InvalidBindingsException (bindings |> Array.map (fun (c, binding) -> toPortBinding model c.Name binding)))

    /// Checks for unbound or ambiguously bound required ports.
    let private invalidRequiredPortBindings (model : Model) (c : Comp) =
        let reqPorts = collect (fun c -> c.Methods |> Seq.filter (fun m -> match m.Kind with ReqPort -> true | _ -> false)) c
        let bindings = collect (fun c -> c.Bindings) c

        let invalid = 
            reqPorts 
            |> Seq.map (fun (c, p) -> (c, p, bindings |> Seq.filter (fun (_, b) -> b.TargetComp = c.Name && b.TargetPort = p.Name) |> Seq.toArray))
            |> Seq.filter (fun (c, p, bindings) -> bindings.Length <> 1)
            |> Seq.toArray

        let unbound = invalid |> Array.filter (fun (c, p, bindings) -> bindings.Length = 0)
        if unbound.Length > 0 then
            raise (UnboundRequiredPortsException (unbound |> Array.map (fun (c, m, _) -> toPortInfo model c.Name m.Name)))

        let ambiguous = invalid |> Array.filter (fun (c, p, bindings) -> bindings.Length > 1)
        if ambiguous.Length > 0 then
            raise (AmbiguousRequiredPortBindingsException (ambiguous |> Array.map (fun (_, _, b) -> b |> Array.map (fun (c, b) -> toPortBinding model c.Name b))))

    /// Checks for cyclic control flow, i.e., ports recursively invoking themselves without a delayed binding in between.
    let private controlFlowCycles (model : Model) (c : Comp) =
        let componentMethodVertex componentName portName = 
            let c = model.FindComponent componentName
            (c, model.MetadataProvider.UnmapMethod (c.GetType ()) portName)

        let edges = List<SEdge<_>> ()
        let edge startVertex endVertex = edges.Add (SEdge<_> (startVertex, endVertex))

        // Compute the edges from the required ports to the instantly bound provided ports
        let required = collect (fun c -> c.Bindings) c |> Seq.filter (fun (c, binding) -> binding.Kind = Instantaneous) |> Seq.iter (fun (c, binding) -> 
            edge (componentMethodVertex binding.TargetComp binding.TargetPort) (componentMethodVertex binding.SourceComp binding.SourcePort)
        )

        let collectInvocations kind = 
            collect (fun c -> c.Methods |> Seq.filter (fun m -> m.Kind = kind)) c 
            |> Seq.iter (fun (c, port) ->
                let edge = edge (componentMethodVertex c.Name port.Name)
                let invocations e =
                    match e with
                    | CallExpr (m, _, _, _, _, _, false) -> edge (componentMethodVertex c.Name m)
                    | TypeExpr (t, CallExpr (m, _, _, _, _, _, false)) -> notSupported "Unsupported static method call '%+A'." e
                    | MemberExpr (Field (f, ClassType _), CallExpr (m, _, _, _, _, _, false)) -> edge (componentMethodVertex f m)
                    | CallExpr (_, _, _, _, _, _, true)
                    | TypeExpr (_, CallExpr (_, _, _, _, _, _, true))
                    | MemberExpr (_, CallExpr (_, _, _, _, _, _, true)) -> notSupported "Unsupported virtual method call '%+A'." e
                    | _ -> ()

                port.Body |> Ssm.iterExprs invocations
            )

        // Compute the edges from the provided ports and step functions to all invoked methods
        let provided = collectInvocations ProvPort
        let step = collectInvocations Step

        let graph = edges.ToAdjacencyGraph ()

        // Check for recursive function calls; this is a special case that is not detected by the
        // SSC-based cycle detection below.
        match graph.Edges |> Seq.tryFind (fun edge -> edge.Source = edge.Target) with
        | None -> ()
        | Some edge -> raise (CyclicControlFlowException [|edge.Source|])

        // Construct the sets of strongly connected components of the graph; if there are no cycles, the
        // number of SCCs matches the number of vertices.
        let mutable components : IDictionary<_,_> = null
        let componentCount = graph.StronglyConnectedComponents (&components)

        if componentCount <> graph.VertexCount then
            // Report the smallest cycle that was found
            let cycle = 
                components 
                |> Seq.map (fun p -> (p.Key, p.Value)) 
                |> Seq.groupBy (fun (_, scc) -> scc) 
                |> Seq.filter (fun (_, scc) -> Seq.length scc > 1)
                |> Seq.minBy (snd >> Seq.length) 
                |> snd
                |> Seq.map fst
                |> Seq.toArray
            raise (CyclicControlFlowException cycle)

    /// Performs the validation of the given SSM root component and S# model.
    let validate (model : Model) (c : Comp) =
        invalidBindings model c
        invalidRequiredPortBindings model c
        controlFlowCycles model c