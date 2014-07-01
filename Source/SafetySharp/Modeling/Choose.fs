// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.InteropServices
open SafetySharp.Internal.Utilities

/// Provides methods for nondeterministic choices.
[<AbstractClass; Sealed>]
type Choose () =

    static member Literal<'T when 'T : struct and 'T :> IComparable and 'T :> IFormattable and 'T :> IConvertible> ([<Out>] result : 'T byref) : 'T =
        raise <| NotImplementedException ()

    static member Boolean ([<Out>] result : bool byref) : bool =
        raise <| NotImplementedException ()

    static member Value ([<Out>] result : int byref, [<ParamArray>] values : int array) : int =
        raise <| NotImplementedException ()

    static member Value ([<Out>] result : decimal byref, [<ParamArray>] values : decimal array) : decimal =
        raise <| NotImplementedException ()

    static member FromRange ([<Out>] result : int byref, inclusiveLowerBound : int, inclusiveUpperBound : int) : int =
        raise <| NotImplementedException ()

    static member FromRange ([<Out>] result : decimal byref, inclusiveLowerBound : decimal, inclusiveUpperBound : decimal) : decimal =
        raise <| NotImplementedException ()

    // ---------------------------------------------------------------------------------------------------------------------------------------
    // The following methods are never invoked at runtime but their definition is required during transformation.                  
    // ---------------------------------------------------------------------------------------------------------------------------------------
    
    static member Literal<'T when 'T : struct and 'T :> IComparable and 'T :> IFormattable and 'T :> IConvertible> () : 'T =
        raise <| NotSupportedException ()

    static member Boolean () : bool =
        raise <| NotSupportedException ()

    static member Value ([<ParamArray>] values : int array) : int =
        raise <| NotSupportedException ()

    static member Value ([<ParamArray>] values : decimal array) : decimal =
        raise <| NotSupportedException ()

    static member FromRange (inclusiveLowerBound : int, inclusiveUpperBound : int) : int =
        raise <| NotSupportedException ()

    static member FromRange (inclusiveLowerBound : decimal, inclusiveUpperBound : decimal) : decimal =
        raise <| NotSupportedException ()