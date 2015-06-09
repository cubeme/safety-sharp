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

namespace Utilities.Assert

open System
open System.Linq
open NUnit.Framework
open SafetySharp.Compiler.Utilities

[<TestFixture>]
module ``That method`` =
    [<Test>]
    let ``throws if message is null`` () =
        raisesArgumentNullException "message" (fun () -> Assert.That (true, null))

    [<Test>]
    let ``throws if condition is false`` () =
        let e = raisesWith<InvalidOperationException> (fun () -> Assert.That (false, "message: {0}", 1))
        e.Message =? "message: 1"

    [<Test>]
    let ``does not throw if condition is true`` () =
        nothrow (fun () -> Assert.That (true, "message: {0}", 1))

[<TestFixture>]
module ``NotReached method`` =
    [<Test>]
    let ``throws when reached`` () =
        let e = raisesWith<InvalidOperationException> (fun () -> Assert.NotReached ("message: {0}", 1))
        e.Message =? "message: 1"

        raises<InvalidOperationException> (fun () -> Assert.NotReached null)

[<TestFixture>]
module ``InRange methods`` =
    type A = X = 1 | Y = 2

    [<Test>]
    let ``throws when a non-enum value is passed`` () =
        raises<InvalidOperationException> (fun () -> Assert.InRange 1)

    [<Test>]
    let ``throws when out-of-range enum value is passed`` () =
        raises<InvalidOperationException> (fun () -> Assert.InRange (enum<A> 17))

    [<Test>]
    let ``does not throw when valid enum value is passed`` () =
        nothrow (fun () -> Assert.InRange A.X)

    [<Test>]
    let ``throws when lower bound exceeds upper bound`` () =
        raisesArgumentException "lowerBound" (fun () -> Assert.InRange (18, 17, 0))

    [<Test>]
    let ``throws on lower bound violation`` () =
        raises<InvalidOperationException> (fun () -> Assert.InRange (0, 1, 5))
        raises<InvalidOperationException> (fun () -> Assert.InRange (0, 10, 50))

    [<Test>]
    let ``throws on upper bound violation`` () =
        raises<InvalidOperationException> (fun () -> Assert.InRange (5, 1, 5))
        raises<InvalidOperationException> (fun () -> Assert.InRange (6, 1, 5))
        raises<InvalidOperationException> (fun () -> Assert.InRange (51, 10, 50))
        raises<InvalidOperationException> (fun () -> Assert.InRange (5, 5, 5))

    [<Test>]
    let ``does not throw when bounds are not violated`` () =
        nothrow (fun () -> Assert.InRange (5, 0, 10))
        nothrow (fun () -> Assert.InRange (5, 5, 6))

    [<Test>]
    let ``throws when collection is null`` () =
        raisesArgumentNullException "collection" (fun () -> Assert.InRange (1, null))

    [<Test>]
    let ``throws on array lower bound violation`` () =
        raises<InvalidOperationException> (fun () -> Assert.InRange (0, [||]))

    [<Test>]
    let ``throws on array upper bound violation`` () =
        raises<InvalidOperationException> (fun () -> Assert.InRange (1, [| 0 |]))
        raises<InvalidOperationException> (fun () -> Assert.InRange (3, [| 0 |]))
        raises<InvalidOperationException> (fun () -> Assert.InRange (3, [| 1; 2 |]))

    [<Test>]
    let ``does not throw when array bounds are not violated`` () =
        nothrow (fun () -> Assert.InRange (1, [| 1; 2; 3 |]))
        nothrow (fun () -> Assert.InRange (0, [| 1 |]))

[<TestFixture>]
module ``OfType method`` =
    [<Test>]
    let ``throws when obj is not of expected type`` () =
        raises<InvalidCastException> (fun () -> Assert.OfType<string>(obj (), null))

        let e = raisesWith<InvalidCastException> (fun () -> Assert.OfType<string>(obj (), "message: {0}", 1))
        e.Message =? "message: 1"

    [<Test>]
    let ``does not throw when obj is of expected type`` () =
        nothrow (fun () -> Assert.OfType<string>("test" :> obj, null))
