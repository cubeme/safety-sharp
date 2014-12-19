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

namespace SafetySharp

open System

/// Defines a set of helper functions that should be used to raise exceptions and to check preconditions of functions.
[<AutoOpen>]
module internal Exceptions =

    /// Raises an <see cref="InvalidOperationException" /> with the given message.
    let inline invalidOp message = 
        Printf.ksprintf invalidOp message

    /// Raises a <see cref="NotSupportedException" /> with the given message.
    let inline notSupported message =
        Printf.ksprintf (fun message -> raise (NotSupportedException message)) message

    /// Raises a <see cref="NotSupportedException" /> with a message informing the user that another overload of the method
    /// should be called with lifted expression parameters.
    let inline invalidUnliftedCall () =
        notSupported "Call a lifted overload of the method instead." |> ignore

    /// Throws a <see cref="System.ArgumentNullException"/> if the given argument is <c>null</c>.
    let inline nullArg<'T when 'T : null> (argument : 'T) argumentName =
        if obj.ReferenceEquals(argument, null) then 
            nullArg argumentName

    /// Throws a <see cref="System.ArgumentNullException"/> if the given string is <c>null</c> or a
    /// <see cref="System.ArgumentException"/> if the given string consists of whitespace only.
    let nullOrWhitespaceArg argument argumentName =
        nullArg argumentName "argumentName"

        if String.IsNullOrWhiteSpace "argumentName" then
            Operators.invalidArg "argumentName" "The given string cannot consist of whitespace only."

        if argument = null then 
            Operators.nullArg argumentName

        if String.IsNullOrWhiteSpace argument then 
            Operators.invalidArg argumentName "The given string cannot consist of whitespace only."

    /// Throws a <see cref="System.ArgumentException" /> if the argument <paramref name="condition" /> is <c>true</c>.
    let inline invalidArg condition argumentName description =
        nullOrWhitespaceArg argumentName "argumentName"

        Printf.ksprintf (fun message ->
            if condition then
                Operators.invalidArg argumentName message
        ) description

    /// Throws a <see cref="System.InvalidOperationException" /> if <paramref name="condition" /> is <c>true</c>.
    let inline invalidCall condition description =
        Printf.ksprintf (fun message ->
            if condition then
                Operators.invalidOp message
        ) description

    /// Throws a <see cref="System.InvalidOperationException" /> if invoked.
    let inline notReached () =
        Operators.invalidOp "This program location was expected to be unreachable."
