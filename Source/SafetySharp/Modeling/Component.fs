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
open System.Runtime.InteropServices

type IComponent = interface end

[<AbstractClass>]
type Component () =
    abstract member Update : unit -> unit
    default this.Update () = ()

    interface IComponent

    static member Choose<'T> ([<Out>] result : 'T byref, [<ParamArray>] values: 'T array) : 'T =
        raise <| NotImplementedException ()

    static member ChooseFromRange ([<Out>] result : int byref, inclusiveLowerBound : int, inclusiveUpperBound : int) : int =
        raise <| NotImplementedException ()

    static member ChooseFromRange ([<Out>] result : decimal byref, inclusiveLowerBound : decimal, inclusiveUpperBound : decimal) : decimal =
        raise <| NotImplementedException ()

    static member Choose<'T when 'T : struct> () : 'T =
        raise <| NotSupportedException ()

    static member Choose<'T> ([<ParamArray>] values : 'T array) : 'T =
        raise <| NotSupportedException ()

    static member ChooseFromRange (inclusiveLowerBound : int, inclusiveUpperBound : int) : int =
        raise <| NotSupportedException ()

    static member ChooseFromRange (inclusiveLowerBound : decimal, inclusiveUpperBound : decimal) : decimal =
        raise <| NotSupportedException ()