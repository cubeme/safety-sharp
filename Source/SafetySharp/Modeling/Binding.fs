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

/// Indicates the kind of a binding.
type BindingKind =
    | Instantaneous 
    | Delayed

/// Provides metadata about a port.
[<AllowNullLiteral>]
type PortInfo internal (c : obj, m : MethodInfo) =
    /// Gets the method representing the port.    
    member this.Method = m

    /// Gets the component instance declaring the bound port.
    member this.Component = c

    /// Gets a value indicating whether the port is a required port.
    member this.IsRequiredPort = Reflection.hasAttribute<RequiredAttribute> this.Method

    /// Creates a new instance for a method port.
    static member MethodPort (port : Delegate) =
        nullArg port "port"
        PortInfo (port.Target, port.Method)

    /// Creates a new instance for a property port.
    static member PropertyPort (port : Delegate) =
        notImplemented ()

/// Represents a binding of two ports. Use the syntax <c>component1.RequiredPorts.Port = component2.ProvidedPorts.Port</c>
/// to instantiate a binding.
[<Sealed; AllowNullLiteral>]
type PortBinding (targetPort : PortInfo, sourcePort : PortInfo) =
    do nullArg sourcePort "sourcePort"
    do nullArg targetPort "targetPort"

    let mutable isSealed = false

    /// Gets the source port of the binding.
    member this.SourcePort = sourcePort

    /// Gets the target port of the binding.
    member this.TargetPort = targetPort

    /// Gets or sets the kind of the binding.
    member val Kind = Instantaneous with get, set

    /// Gets or sets the object that instantiated the binding.
    member val Binder = (null : obj) with get, set

    /// Finalizes the bindings's metadata, disallowing any future metadata modifications.
    member internal this.FinalizeMetadata () =
        invalidCall isSealed "The port binding's metadata has already been finalized."
        isSealed <- true

    /// Changes the kind of the binding to delayed, meaning that the invocation of the bound port is delayed by one system step.
    member this.Delayed () =
        invalidCall isSealed "Modifications of the port binding's metadata are only allowed during object construction."
        this.Kind <- Delayed