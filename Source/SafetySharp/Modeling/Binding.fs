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

namespace SafetySharp.Modeling

open System
open System.Collections.Generic
open System.Dynamic
open System.Globalization
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.InteropServices
open SafetySharp
open SafetySharp.Modeling.CompilerServices
open Mono.Cecil

/// Represents a binding of two ports. Use the syntax <c>component1.RequiredPorts.Port = component2.ProvidedPorts.Port</c>
/// to instantiate a binding.
[<AllowNullLiteral; AbstractClass>]
type PortBinding () =
    class end

///// Represents a port.
//[<AllowNullLiteral>]
//type Port (comp: obj, port : MethodInfo) =
//    /// Gets the component the port belongs to.
//    member val Component = comp with get
//
//    /// Gets the name of the port.
//    member this.Name with get () = port.Name
//
//    /// Gets the return type of the port.
//    member this.ReturnType with get () = port.ReturnType
//
//    /// Gets the parameters of the port.
//    member this.Parameters with get () = port.GetParameters () |> List.ofArray
//
//    /// Gets the underlying method that represents the port.
//    member this.Method with get () = port
//
//    /// Gets a value indicating whether the port is a required port
//    member this.IsRequiredPort with get () = Reflection.hasAttribute<RequiredAttribute> port
//
//    /// Gets a value indicating whether the port is a provided port
//    member this.IsProvidedPort with get () = Reflection.hasAttribute<ProvidedAttribute> port
//
//    /// Checks whether the two ports are signature-compatible.
//    member this.IsCompatibleTo (other : Port) =
//        this.IsCompatibleTo other.Method
//
//    /// Checks whether the port is signature-compatible to the given method.
//    member this.IsCompatibleTo (other : MethodInfo) =
//        let parametersMatch (p1 : ParameterInfo, p2 : ParameterInfo) =
//            p1.ParameterType = p2.ParameterType && p1.IsIn = p2.IsIn && p1.IsOut = p2.IsOut
//
//        let parameters = other.GetParameters ()
//        this.ReturnType = other.ReturnType && this.Parameters.Length = parameters.Length &&
//            Seq.zip this.Parameters parameters |> Seq.forall parametersMatch
//
///// Represents a set of ports with the same name.
//[<AllowNullLiteral>]
//type PortSet (name : string, comp : obj, ports : MethodInfo seq) =
//    /// Gets the component the ports belong to.
//    member this.Component with get() = comp
//
//    /// Gets the name of the ports.
//    member this.Name with get() = name
//
//    /// Gets the ports contained in the set.
//    member val Ports = ports |> Seq.map (fun p -> Port (comp, p)) |> Seq.toList with get
//
//    /// Gets a port with the given signature.
//    member this.OfType<'T> () = 
//        let portType = typeof<'T>.GetMethod "Invoke"
//
//        match this.Ports |> List.tryFind (fun p -> p.IsCompatibleTo portType) with
//        | None   -> invalidOp "Unable to find a port with the given signature."
//        | Some p -> p
//
//    /// Tries to find a port with the a compatible signature.
//    member this.FindCompatiblePort (port : Port) = 
//        let portType = port.Method
//        this.Ports |> List.tryFind (fun p -> p.IsCompatibleTo port.Method)
//
///// Raised when a port binding could not be established.
//type BindingFailureException internal (targets : Port list, sources : Port list) =
//    inherit Exception ("Port binding failed: No signature-compatible ports could be found. See the 'TargetPorts' \
//            and 'SourcePorts' properties for a list of ports that were considered while trying to establish the binding.")
//
//    /// Gets the target port candidates of the attempted binding.
//    member this.TargetPorts = targets |> Array.ofList
//
//    /// Gets the source port candidates of the attempted binding.
//    member this.SourcePorts = sources |> Array.ofList
//
///// Raised when a port binding could not be established because of ambiguous matches.
//type AmbiguousBindingException internal (targets : Port list, sources : Port list) =
//    inherit Exception ("Port binding is ambiguous. You can disambiguate the binding using the 'OfType<DelegateType>()' \
//            method on one of the given ports. For instance, use 'RequiredPorts.X = ProvidedPorts.Y.OfType<Action>'() \
//            if the port you want to bind is signature-compatible to the 'System.Action' delegate. See the 'TargetPorts' \
//            and 'SourcePorts' properties for a list of ports that were considered while trying to establish the binding.")
//
//    /// Gets the target port candidates of the attempted binding.
//    member this.TargetPorts = targets |> Array.ofList
//
//    /// Gets the source port candidates of the attempted binding.
//    member this.SourcePorts = sources |> Array.ofList
//
///// Represents a collection of required ports. Allows a binding for a required port to be specified using 
///// C#'s dynamic member assignment operations.
//type internal RequiredPortCollection (comp : obj) =
//    inherit DynamicObject ()
//    do nullArg comp "comp"
//
//    /// The established bindings.
//    let bindings = Dictionary<Port, Port> ()
//
//    /// The required ports declared by the component grouped by name.
//    let ports =
//        Reflection.getMethods (comp.GetType ())
//        |> Seq.filter Reflection.hasAttribute<RequiredAttribute>
//        |> Seq.groupBy (fun p -> p.Name)
//        |> Seq.map (fun (name, ports) -> (name, PortSet (name, comp, ports)))
//        |> Map.ofSeq
//
//    /// Gets the required ports declared by the component grouped by name.
//    member this.GetPortSets () =
//        ports |> Map.toSeq |> Seq.map snd |> Seq.toList
//
//    /// Gets all bindings that have been established.
//    member this.Bindings with get () = bindings |> Seq.map (fun p -> (p.Key, p.Value)) |> Seq.toList
//
//    /// Clears all bindings that have been established.
//    member this.ClearBindings () =
//        bindings.Clear ()
//
//    /// Tries to establish a binding between the requested required port set and the given provided port set.
//    override this.TrySetMember (binder, providedPort) =
//        nullArg providedPort "providedPort"
//
//        match ports |> Map.tryFind binder.Name with
//        | None   -> false
//        | Some reqPorts -> 
//            match providedPort with
//            | :? PortSet as provPorts -> this.Bind reqPorts.Ports provPorts.Ports
//            | :? Port as provPort     -> this.Bind reqPorts.Ports [provPort]
//            | _                       -> invalidArg true "value" "Expected a port."; false
//
//    /// Tries to uniquely determine a pair of signature-compatible ports and establishes a binding between the two,
//    /// overiding any previously set binding of the given required port.
//    member this.Bind (reqPorts : Port list) (provPorts : Port list) =
//        let candidates = 
//            reqPorts
//            |> Seq.map (fun r -> (r, provPorts |> List.tryFind (fun p -> p.IsCompatibleTo r)))
//            |> Seq.filter (fun (r, p) -> p <> None)
//            |> Seq.toList
//
//        match candidates with
//        | []                -> BindingFailureException (reqPorts, provPorts) |> raise
//        | (r, Some p) :: [] -> bindings.[r] <- p; true
//        | _                 -> AmbiguousBindingException (reqPorts, provPorts) |> raise
//
///// Represents a collection of provided ports. Allows the retrieval of a port using C#'s dynamic member access.
//type internal ProvidedPortCollection (comp : obj) =
//    inherit DynamicObject ()
//    do nullArg comp "comp"
//
//    /// The provided ports declared by the component grouped by name.
//    let ports =
//        Reflection.getMethods (comp.GetType ())
//        |> Seq.filter Reflection.hasAttribute<ProvidedAttribute>
//        |> Seq.groupBy (fun p -> p.Name)
//        |> Seq.map (fun (name, ports) -> (name, PortSet (name, comp, ports)))
//        |> Map.ofSeq
//
//    /// Gets the provided ports declared by the component grouped by name.
//    member this.GetPortSets () =
//        ports |> Map.toSeq |> Seq.map snd |> Seq.toList
//
//    /// Tries to get the requested provided port set.
//    override this.TryGetMember (binder, providedPort) =
//        match ports |> Map.tryFind binder.Name with
//        | None   -> false
//        | Some p -> providedPort <- p; true