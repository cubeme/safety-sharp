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

namespace SafetySharp.Internal.Metamodel

/// Represents the operator of an unary temporal formula.
type internal UnaryFormulaOperator =
    // Non-temporal operators
    | Not

    // LTL temporal operators
    | Next
    | Finally
    | Globally

    // CTL temporal operators
    | AllPathsNext
    | AllPathsFinally
    | AllPathsGlobally
    | ExistsPathNext
    | ExistsPathFinally
    | ExistsPathGlobally

/// Represents the operator of a binary temporal formula.
type internal BinaryFormulaOperator =
    // Non-temporal operators
    | And
    | Or
    | Implication
    | Equivalence

    // LTL temporal operator
    | Until

    // CTL temporal operators
    | AllPathsUntil
    | ExistsPathUntil

/// Represents a temporal formula, either in computation tree logic format or linear temporal logic format.
type internal Formula =
    /// Represents a state formula that is evaluated in a single model state.
    | StateFormula of StateExpression : Expression

    /// Represents the application of an unary formula operator to a formula.
    | UnaryFormula of Operand : Formula * Operator : UnaryFormulaOperator

    /// Represents the application of a binary formula operator to two subformulas.
    | BinaryFormula of LeftFormula : Formula * Operator : BinaryFormulaOperator * RightFormula : Formula

    with 

    /// Gets a value indicating whether the formula is a valid linear temporal logic formula.
    member this.IsLtl () = 
        match this with
        | StateFormula _ -> 
            true
        | UnaryFormula (operand, operator) ->
            (operator = Not || operator = Next || operator = Finally || operator = Globally) && operand.IsLtl ()
        | BinaryFormula (left, operator, right) ->
            operator <> AllPathsUntil && operator <> ExistsPathUntil && left.IsLtl () && right.IsLtl ()

    /// Gets a value indicating whether the formula is a valid computation tree logic formula.
    member this.IsCtl () = 
        match this with
        | StateFormula _ -> 
            true
        | UnaryFormula (operand, operator) ->
            operator <> Next && operator <> Finally && operator <> Globally && operand.IsCtl ()
        | BinaryFormula (left, operator, right) ->
            operator <> Until && left.IsCtl () && right.IsCtl ()
