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

/// Performs a couple of validation checks on a lowered SSM model.
module internal SsmValidation =
    open System
    open System.Reflection
    open SafetySharp
    open SafetySharp.Modeling
    open Ssm
    open QuickGraph
    open QuickGraph.Algorithms

    /// Raised when one or more invalid port bindings were encountered.
    type InvalidBindingsException internal (invalidBindings : PortBinding array) =
        inherit Exception ("One or more bindings are invalid. A binding can only be established if it does not span more than one level \
            of the hierarchy. Use the 'InvalidBindings' property to inspect the bindings this exception was raised for.")

        /// Gets the invalid port bindings the exception was raised for.
        member this.InvalidBindings = invalidBindings

    /// Raised when one or more unbound required ports were found.
    type UnboundRequiredPortsException internal (unboundPorts : PortInfo array) =
        inherit Exception ("One or more unbound required ports detected. Use the 'UnboundPorts' property to inspect the required ports \
            this exception was raised for.")

        /// Gets the unbound required ports the exception was raised for.
        member this.UnboundPorts = unboundPorts

    /// Raised when one or more required ports have more than one binding.
    type AmbiguousRequiredPortBindingsException internal (ambiguousBindings : PortBinding array array) =
        inherit Exception ("Detected an ambiguous binding for one or more required ports. Use the 'AmbiguousBindings' property to inspect \
            the required ports and bindings this exception was raised for.")

        /// Gets the unbound required ports the exception was raised for.
        member this.AmbiguousBindings = ambiguousBindings

    /// Maps the given information to a PortInfo instance.
    let toPortInfo (m : Model) (componentName : string) (portName : string) =
        () //TODO

    /// Selects all elements from the given component hierarchy using the given selector function.
    let rec collectAll selector (c : Comp) = seq {
        yield! selector c |> Seq.map (fun e -> (c, e))
        yield! c.Subs |> Seq.collect (collectAll selector)
    }

    /// Checks for invalid bindings, i.e., bindings spanning more than one level of the component hierarchy.
    let private invalidBindings (m : Model) (c : Comp) =
        let rec check (c : Comp) = seq {
            let invalidComp portComponent = c.Name <> portComponent && c.Subs |> List.exists (fun s -> s.Name = portComponent) |> not
            yield! c.Bindings 
                   |> Seq.filter (fun binding -> invalidComp binding.SourceComp || invalidComp binding.TargetComp) 
                   |> Seq.map (fun binding -> (c, binding))
            yield! c.Subs |> Seq.map check |> Seq.collect id
        }

        let bindings = check c |> Seq.toArray
        if bindings.Length > 0 then
            //bindings |> Array.map (fun binding -> PortBinding ()) // TODO
            raise (InvalidBindingsException ([||])) // TODO

    /// Checks for unbound or ambiguously bound required ports.
    let private invalidRequiredPortBindings (m : Model) (c : Comp) =
        let reqPorts = collectAll (fun c -> c.Methods |> Seq.filter (fun m -> match m.Kind with ReqPort -> true | _ -> false)) c
        let bindings = collectAll (fun c -> c.Bindings) c

        let invalid = 
            reqPorts 
            |> Seq.map (fun (c, p) -> (c, p, bindings |> Seq.filter (fun (_, b) -> b.SourceComp = c.Name && b.SourcePort = p.Name) |> Seq.length))
            |> Seq.filter (fun (c, p, count) -> count <> 1)
            |> Seq.toArray

        let unbound = invalid |> Array.filter (fun (c, p, count) -> count = 0)
        if invalid.Length > 0 then
            //bindings |> Array.map (fun binding -> PortBinding ()) // TODO
            raise (UnboundRequiredPortsException ([||])) // TODO

        let ambiguous = invalid |> Array.filter (fun (c, p, count) -> count > 1)
        if ambiguous.Length > 0 then
            //bindings |> Array.map (fun binding -> PortBinding ()) // TODO
            raise (AmbiguousRequiredPortBindingsException ([||])) // TODO

    /// Checks for cyclic control flow, i.e., ports recursively invoking themselves without a delayed binding in between.
    let private controlFlowCycles (m : Model) (c : Comp) =
        let createVertex = sprintf "%s.%s"

        // Compute the edges from the required ports to the bound provided ports
        let required =
            collectAll (fun c -> c.Bindings) c |> Seq.map (fun (c, binding) -> 
                SEdge<_> (createVertex binding.SourceComp binding.SourcePort, createVertex binding.TargetComp binding.TargetPort)
            )

        // Compute the edges from the provided ports to all invoked methods
        ()

    /// Performs the validation of the given SSM root component and S# model.
    let validate (m : Model) (c : Comp) =
        invalidBindings m c
        invalidRequiredPortBindings m c
        controlFlowCycles m c