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
open System.Linq.Expressions
open SafetySharp.Metamodel

/// Represents a linear temporal logic formula provided by a C# model.
type internal CSharpFormula =
    /// Represents a state formula that is evaluated in a single model state.
    | CSharpStateFormula of StateExpression : Expression<Func<bool>>

    /// Represents the application of an unary formula operator to a formula.
    | CSharpUnaryFormula of Operand : CSharpFormula * Operator : UnaryFormulaOperator

    /// Represents the application of a binary formula operator to two subformulas.
    | CSharpBinaryFormula of LeftFormula : CSharpFormula * Operator : BinaryFormulaOperator * RightFormula : CSharpFormula

/// Raised when a component referenced in a formula is not contained within the model the formula is created for.
type UnknownComponentException internal (unknownComponent : IComponent) =
    inherit Exception ("The formula references a component that is not contained within the model the formula is created for.")

    /// Gets the unknown component instances that was found in the formula.
    member this.UnknownComponent = unknownComponent