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

namespace Utilities.Requires

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open SafetySharp.Utilities

[<AutoOpen>]
module Helpers =
    type A = X = 1 | Y = 2

    type X () =
        [<DefaultValue>] val mutable i : int
        [<DefaultValue>] val mutable s : string
        [<DefaultValue>] val mutable a : A
        [<DefaultValue>] val mutable o : obj

    let argumentName<'T> fieldName = 
        let fieldInfo = typeof<X>.GetField(fieldName, BindingFlags.Public ||| BindingFlags.Instance)
        Expression.Lambda<Func<'T>>(Expression.MakeMemberAccess(Expression.Constant(X ()), fieldInfo))

    let argumentNameInt = argumentName<int> "i"
    let argumentNameString = argumentName<string> "s"
    let argumentNameEnum = argumentName<A> "a"
    let argumentNameObj = argumentName<obj> "o"

[<TestFixture>]
module ``NotNull method`` =
    [<Test>]    
    let ``throws if argumentName is null`` () =
        raisesArgumentNullException "argumentName" (fun () -> Requires.NotNull (obj (), null))

    [<Test>]    
    let ``throws if obj is null`` () =
        raisesArgumentNullException "s" (fun () -> Requires.NotNull (null, argumentNameString))

    [<Test>]
    let ``does not throw if obj is not null`` () =
        nothrow (fun () -> Requires.NotNull ("", argumentNameString))

[<TestFixture>]
module ``NotNullOrWhitespace method`` =
    [<Test>]    
    let ``throws if argumentName is null`` () =
        raisesArgumentNullException "argumentName" (fun () -> Requires.NotNullOrWhitespace ("a", null))

    [<Test>]    
    let ``throws if string is null`` () =
        raisesArgumentNullException "s" (fun () -> Requires.NotNullOrWhitespace (null, argumentNameString))

    [<Test>]    
    let ``throws if string is empty`` () =
        raisesArgumentException "s" (fun () -> Requires.NotNullOrWhitespace ("", argumentNameString))
        raisesArgumentException "s" (fun () -> Requires.NotNullOrWhitespace ("  ", argumentNameString))
        raisesArgumentException "s" (fun () -> Requires.NotNullOrWhitespace ("       \n ", argumentNameString))

    [<Test>]
    let ``does not throw if string is neither null nor empty`` () =
        nothrow (fun () -> Requires.NotNullOrWhitespace ("a", argumentNameString))

[<TestFixture>]
module ``That method`` =
    [<Test>]
    let ``throws if message is null`` () =
        raisesArgumentNullException "message" (fun () -> Requires.That (true, null))

    [<Test>]
    let ``throws if condition is false`` () =
        let e = raisesWith<InvalidOperationException> (fun () -> Requires.That (false, "message: {0}", 1))
        e.Message =? "message: 1"

    [<Test>]
    let ``does not throw if condition is true`` () =
        nothrow (fun () -> Requires.That (true, "message: {0}", 1))

[<TestFixture>]
module ``ArgumentSatisfies method`` =
    [<Test>]    
    let ``throws if argumentName is null`` () =
        raisesArgumentNullException "argumentName" (fun () -> Requires.ArgumentSatisfies (true, null, null))

    [<Test>]
    let ``throws if condition is false`` () =
        raisesArgumentException "i" (fun () -> Requires.ArgumentSatisfies (false, argumentNameInt, null))
        let e = raisesWith<ArgumentException> (fun () -> Requires.ArgumentSatisfies (false, argumentNameInt, "message: {0}", 1))
        e.Message.StartsWith "message: 1" =? true
        e.ParamName =? "i"

    [<Test>]
    let ``does not throw if condition is true`` () =
        nothrow (fun () -> Requires.ArgumentSatisfies (true, argumentNameInt, "message: {0}", 1))

[<TestFixture>]
module ``InRange methods`` =
    [<Test>]    
    let ``throws if argumentName is null`` () =
        raisesArgumentNullException "argumentName" (fun () -> Requires.InRange (A.X, null))
        raisesArgumentNullException "argumentName" (fun () -> Requires.InRange (1, null, 1, 2))
        raisesArgumentNullException "argumentName" (fun () -> Requires.InRange (0, null, [| 1 |]))

    [<Test>]
    let ``throws when a non-enum value is passed`` () =
        raisesArgumentException "i" (fun () -> Requires.InRange (1, argumentNameInt))

    [<Test>]
    let ``throws when out-of-range enum value is passed`` () =
        raisesArgumentException "a" (fun () -> Requires.InRange (enum<A> 17, argumentNameEnum))

    [<Test>]
    let ``does not throw when valid enum value is passed`` () =
        nothrow (fun () -> Requires.InRange (A.X, argumentNameEnum))

    [<Test>]
    let ``throws when lower bound exceeds upper bound`` () =
        raisesArgumentException "lowerBound" (fun () -> Requires.InRange (18, argumentNameInt, 17, 0))

    [<Test>]
    let ``throws on lower bound violation`` () =
        raisesArgumentException "i" (fun () -> Requires.InRange (0, argumentNameInt, 1, 5))
        raisesArgumentException "i" (fun () -> Requires.InRange (0, argumentNameInt, 10, 50))

    [<Test>]
    let ``throws on upper bound violation`` () =
        raisesArgumentException "i" (fun () -> Requires.InRange (5, argumentNameInt, 1, 5))
        raisesArgumentException "i" (fun () -> Requires.InRange (6, argumentNameInt, 1, 5))
        raisesArgumentException "i" (fun () -> Requires.InRange (51, argumentNameInt, 10, 50))
        raisesArgumentException "i" (fun () -> Requires.InRange (5, argumentNameInt, 5, 5))

    [<Test>]
    let ``does not throw when bounds are not violated`` () =
        nothrow (fun () -> Requires.InRange (5, argumentNameInt, 0, 10))
        nothrow (fun () -> Requires.InRange (5, argumentNameInt, 5, 6))

    [<Test>]
    let ``throws when collection is null`` () =
        raisesArgumentNullException "collection" (fun () -> Requires.InRange(1, argumentNameInt,  null))

    [<Test>]
    let ``throws on array lower bound violation`` () =
        raisesArgumentException "i" (fun () -> Requires.InRange (0, argumentNameInt, [||]))

    [<Test>]
    let ``throws on array upper bound violation`` () =
        raisesArgumentException "i" (fun () -> Requires.InRange (1, argumentNameInt, [| 0 |]))
        raisesArgumentException "i" (fun () -> Requires.InRange (3, argumentNameInt, [| 0 |]))
        raisesArgumentException "i" (fun () -> Requires.InRange (3, argumentNameInt, [| 1; 2 |]))

    [<Test>]
    let ``does not throw when array bounds are not violated`` () =
        nothrow (fun () -> Requires.InRange (1, argumentNameInt, [| 1; 2; 3 |]))
        nothrow (fun () -> Requires.InRange (0, argumentNameInt, [| 1 |]))

[<TestFixture>]
module ``OfType method`` =
    [<Test>]    
    let ``throws if argumentName is null`` () =
        raisesArgumentNullException "argumentName" (fun () -> Requires.OfType<string> ("", null, null))

    [<Test>]
    let ``throws when obj is not of expected type`` () =
        raisesArgumentException "o" (fun () -> Requires.OfType<string>(obj (), argumentNameObj, null))

        let e = raisesWith<ArgumentException> (fun () -> Requires.OfType<string>(obj (), argumentNameObj, "message: {0}", 1))
        e.Message.StartsWith "message: 1" =? true
        e.ParamName =? "o"

    [<Test>]
    let ``does not throw when obj is of expected type`` () =
        nothrow (fun () -> Requires.OfType<string>("test" :> obj, argumentNameObj, null))
