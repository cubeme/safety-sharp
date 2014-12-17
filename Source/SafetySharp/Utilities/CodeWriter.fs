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
open System.Text

/// Generates code in an in-memory buffer.
type CodeWriter () =
    let output = new StringBuilder()
    let mutable atBeginningOfLine = true
    let mutable indent = 0

    /// Appends the given format string to the current line.
    member public this.Append (s, [<ParamArray>] args) =
        this.AddIndentation ()
        output.AppendFormat (s, args) |> ignore

    /// Appends the given format string to the current line and starts a new line.
    member public this.AppendLine (s, [<ParamArray>] args) =
        this.Append (s, args)
        this.NewLine ()

    /// Appends a new line to the buffer.
    member public this.NewLine () =
        output.AppendLine () |> ignore
        atBeginningOfLine <- true

    /// Appends the given content to the buffer, enclosed in parentheses.
    member public this.AppendParenthesized content =
        this.Append "("
        content ()
        this.Append ")"

    /// Appends a block statement to the buffer, i.e., generates a set of curly braces on separate lines,
    /// increases the indentation and generates the given content within the block.
    member public this.AppendBlockStatement content =
        this.EnsureNewLine ()
        this.AppendLine "{"
        this.IncreaseIndent ()

        content ()

        this.EnsureNewLine ()
        this.DecreaseIndent ()
        this.Append "}"

        this.NewLine ()

    /// Increases the indentation level, starting with the next line.
    member public this.IncreaseIndent() = indent <- indent + 1

    /// Decreases the indentation level, starting with the next line.
    member public this.DecreaseIndent() = indent <- indent - 1

    /// Gets the generated code as a string.
    override this.ToString () =
        output.ToString ()

    member private this.EnsureNewLine() =
        if not atBeginningOfLine then
            this.NewLine ()

    member private this.AddIndentation() =
        if atBeginningOfLine then
            atBeginningOfLine <- false
        for i = 1 to indent do
            output.Append (" ") |> ignore