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

namespace SafetySharp.Utilities
open System

/// Defines a set of helper functions that should be used to assert preconditions of functions.
[<RequireQualifiedAccess>]
module internal Requires =

    /// Throws a <see cref="System.ArgumentNullException"/> if the given argument is <c>null</c>.
    let NotNull<'T when 'T : null> (argument : 'T) argumentName =
        if obj.ReferenceEquals(argument, null) then 
            nullArg argumentName

    /// Throws a <see cref="System.ArgumentNullException"/> if the given string is <c>null</c> or a
    /// <see cref="System.ArgumentException"/> if the given string consists of whitespace only.
    let NotNullOrWhitespace argument argumentName =
        NotNull argumentName "argumentName"

        if String.IsNullOrWhiteSpace "argumentName" then
            invalidArg "argumentName" "The given string cannot consist of whitespace only."

        if argument = null then 
            nullArg argumentName

        if String.IsNullOrWhiteSpace argument then 
            invalidArg argumentName "The given string cannot consist of whitespace only."

    /// Throws a <see cref="System.ArgumentException" /> if the argument <paramref name="condition" /> is <c>false</c>.
    let ArgumentSatisfies condition argumentName description =
        NotNullOrWhitespace argumentName "argumentName"
        NotNullOrWhitespace description "description"
        if not condition then
            invalidArg argumentName description

    /// Throws an <see cref="ArgumentException" /> if <paramref name="argument" /> is not of type <typeparamref name="T" />.
    let OfType<'T when 'T : not struct> (argument : obj) argumentName description =
        NotNull argument "argument"
        NotNullOrWhitespace argumentName "argumentName"
        NotNullOrWhitespace description "description"
        
        if not <| argument :? 'T then
            sprintf "Expected an instance of type '%s' but found an instance of type '%s' instead." typeof<'T>.FullName <| argument.GetType().FullName
            |> invalidArg argumentName

    /// Throws a <see cref="System.InvalidOperationException" /> if <paramref name="condition" /> is <c>false</c>.
    let That condition description =
        NotNullOrWhitespace description "description"
        if not condition then
            invalidOp description