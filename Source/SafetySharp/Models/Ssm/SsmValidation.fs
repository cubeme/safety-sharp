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
open SafetySharp.Modeling

/// Raised when one or more invalid port bindings were encountered that span more than one level of the component hierarchy.
type InvalidBindingsException internal (invalidBindings : PortBinding array) =
    inherit Exception (
        let bindings = String.Join ("\n", invalidBindings |> Array.map (fun binding ->
            sprintf "Component '%s', Port '%A' = Component '%s', Port '%A' [%A]; binding established by Component '%s'"
                (binding.TargetPort.Component :?> Component).UnmangledName binding.TargetPort.Method
                (binding.SourcePort.Component :?> Component).UnmangledName binding.SourcePort.Method
                binding.Kind (binding.Component :?> Component).UnmangledName
        ))
        sprintf "One or more bindings are invalid because they span more than one level of the hierarchy:\n%s\n\
                 Use the 'InvalidBindings' property of this exception instance for further details about the invalid bindings." bindings)

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
                    (binding.SourcePort.Component :?> Component).UnmangledName binding.SourcePort.Method binding.Kind 
                    (binding.Component :?> Component).UnmangledName)
            )
            sprintf "Component '%s', Port '%A':\n     %s" 
                (bindings.[0].TargetPort.Component :?> Component).UnmangledName bindings.[0].TargetPort.Method ambiguousBindings
        ))
        sprintf "Detected an ambiguous binding for one or more required ports:\n%s\nCheck the 'AmbiguousBindings' property of this exception instance \
                 for further details about the ambiguous port bindings." bindings)

    /// Gets the unbound required ports the exception was raised for.
    member this.AmbiguousBindings = ambiguousBindings

/// Performs a couple of validation checks on a lowered SSM model.
module internal SsmValidation =
    open System
    open System.Reflection
    open SafetySharp
    open SafetySharp.Modeling
    open Ssm
    open QuickGraph
    open QuickGraph.Algorithms

    /// Maps the given information to a <see cref="PortInfo" /> instance.
    let private toPortInfo (model : Model) (componentName : string) (portName : string) = 
        let c = model.FindComponent componentName
        PortInfo (c, CilToSsm.unmapMethod c portName)

    /// Maps the given information to a <see cref="PortBinding" /> instance.
    let private toPortBinding (model : Model) (componentName : string) (binding : Binding) =
        let portBinding = PortBinding (toPortInfo model binding.TargetComp binding.TargetPort, toPortInfo model binding.SourceComp binding.SourcePort)
        portBinding.Kind <- binding.Kind
        portBinding.Component <- model.FindComponent componentName
        portBinding

    /// Selects all elements from the given component hierarchy using the given selector function.
    let rec private collect selector (c : Comp) = seq {
        yield! selector c |> Seq.map (fun e -> (c, e))
        yield! c.Subs |> Seq.collect (collect selector)
    }

    /// Checks for invalid bindings, i.e., bindings spanning more than one level of the component hierarchy.
    let private invalidBindings (model : Model) (c : Comp) =
        let rec check (c : Comp) = seq {
            let invalidComp portComponent = c.Name <> portComponent && c.Subs |> List.exists (fun s -> s.Name = portComponent) |> not
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
        let createVertex = sprintf "%s.%s"

        // Compute the edges from the required ports to the bound provided ports
        let required =
            collect (fun c -> c.Bindings) c |> Seq.map (fun (c, binding) -> 
                SEdge<_> (createVertex binding.SourceComp binding.SourcePort, createVertex binding.TargetComp binding.TargetPort)
            )

        // Compute the edges from the provided ports to all invoked methods
        ()

    /// Performs the validation of the given SSM root component and S# model.
    let validate (model : Model) (c : Comp) =
        invalidBindings model c
        invalidRequiredPortBindings model c
        controlFlowCycles model c