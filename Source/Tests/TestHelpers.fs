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

namespace SafetySharp.Tests

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open SafetySharp.Modeling
open Swensen.Unquote
open SafetySharp.Metamodel

[<AutoOpen>]
module TestHelpers =
    
    /// Raises an <see cref="InvalidOperationException" /> with the given message.
    let inline invalidOp message = Printf.ksprintf invalidOp message

    /// Checks whether the given quoted expression raises an <see cref="ArgumentNullException"/> for the argument
    /// with the given name.
    let raisesArgumentNullException argumentName quotedExpression =
        raisesWith<ArgumentNullException> quotedExpression (fun e -> <@ e.ParamName = argumentName @>)

    /// Checks whether the given quoted expression raises an <see cref="ArgumentException"/> for the argument
    /// with the given name.
    let raisesArgumentException argumentName quotedExpression =
        raisesWith<ArgumentException> quotedExpression (fun e -> <@ e.ParamName = argumentName @>)

    /// Gets the symbol for the empty Update method of a component.
    let emptyUpdateMethodSymbol = 
        { Name = "Update"; ReturnType = None; Parameters = [] }

    /// Gets a component symbol with the given component name, with an empty update method and no fields or subcomponents.
    let emptyComponentSymbol name = { 
        Name = sprintf "%s::%s" TestCompilation.CompilationName name
        UpdateMethod = emptyUpdateMethodSymbol
        Fields = []
        Methods = []
    } 

    /// Gets a component object with the given name and component symbol, with no fields or subcomponents.
    let emptyComponentObject name symbol = 
        { Name = name; ComponentSymbol = symbol; Fields = Map.empty; Subcomponents = Map.empty }