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

/// Provides metadata about a port.
type PortInfo private (port : Delegate, backingField : string) =
    /// Gets a value indicating whether the port is a required port.
    member this.IsRequiredPort = backingField <> null

    /// Creates an instance for a required port.
    static member RequiredPort (port : Delegate) =
        nullArg port "port"
        PortInfo (port, null)

    /// Creates an instance for a provided port.
    static member ProvidedPort (port : Delegate) =
        nullArg port "port"
        PortInfo (port, null)

/// Represents a binding of two ports. Use the syntax <c>component1.RequiredPorts.Port = component2.ProvidedPorts.Port</c>
/// to instantiate a binding.
[<Sealed>]
type PortBinding (port1 : PortInfo, port2 : PortInfo) =
    /// Gets the first port that has been bound.
    member internal this.Port1 = port1

    /// Gets the second port that has been bound.
    member internal this.Port2 = port2