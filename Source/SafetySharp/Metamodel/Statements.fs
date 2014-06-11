﻿// The MIT License (MIT)
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

namespace SafetySharp.Metamodel

/// Represents statements contained within method bodies.
type internal Statement =
    /// Represents the empty statement that does nothing.
    | EmptyStatement

    /// Represents a block of statements that are executed sequentially.
    | BlockStatement of Statements : Statement list

    /// Represents a return statement that ends the execution of a method, optionally returning a value.
    | ReturnStatement of Expression : Expression option

    /// Represents a guarded command statement. The body of at most one clause of the guarded command is
    /// executed. For a body to be executed, its guard must evaluate to true. If multiple guards hold, one
    /// clause is chosen nondeterministically.
    | GuardedCommandStatement of (Expression * Statement) list

    /// Represents the assignment of a value to an assignment target, i.e., a field, for instance.
    | AssignmentStatement of Target : Expression * Expression : Expression

    with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this

/// Maps a method symbol to its method body.
type internal MethodBodyResolver = Map<MethodSymbol, Statement>