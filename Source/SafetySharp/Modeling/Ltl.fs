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
open SafetySharp.Utilities
open SafetySharp.Metamodel

/// Represents a linear temporal logic formula provided by a C# model.
type internal CSharpFormula =
    /// Represents a state formula that is evaluated in a single model state.
    | StateFormula of StateExpression : Expression<Func<bool>>

    /// Represents the application of an unary formula operator to a formula.
    | UnaryFormula of Operand : CSharpFormula * Operator : UnaryFormulaOperator

    /// Represents the application of a binary formula operator to two subformulas.
    | BinaryFormula of LeftFormula : CSharpFormula * Operator : BinaryFormulaOperator * RightFormula : CSharpFormula

/// Represents a linear temporal logic formula provided by a C# model.
[<AllowNullLiteral>]
type LtlFormula internal (formula : CSharpFormula) = 
    /// Gets the wrapped C# formula.
    member internal this.Formula = formula

    /// Applies the implication operator to this instance and the given formula.
    member this.Implies (formula : LtlFormula) = 
        LtlFormula (BinaryFormula(this.Formula, BinaryFormulaOperator.Implication, formula.Formula))

/// Provides factory methods for the construction of linear temporal logic formulas.
[<AbstractClass; Sealed>]
type Ltl =

    /// Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
    static member Next (operand : LtlFormula) =
        Requires.NotNull operand "operand"
        LtlFormula (UnaryFormula(operand.Formula, UnaryFormulaOperator.Next))

    /// Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
    static member Next (operand : Expression<Func<bool>>) =
        Requires.NotNull operand "operand"
        LtlFormula (UnaryFormula(StateFormula operand, UnaryFormulaOperator.Next))

    /// Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
    static member Finally (operand : LtlFormula) =
        Requires.NotNull operand "operand"
        LtlFormula (UnaryFormula(operand.Formula, UnaryFormulaOperator.Finally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
    static member Finally (operand : Expression<Func<bool>>) =
        Requires.NotNull operand "operand"
        LtlFormula (UnaryFormula(StateFormula operand, UnaryFormulaOperator.Finally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
    static member Globally (operand : LtlFormula) =
        Requires.NotNull operand "operand"
        LtlFormula (UnaryFormula(operand.Formula, UnaryFormulaOperator.Globally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
    static member Globally (operand : Expression<Func<bool>>) =
        Requires.NotNull operand "operand"
        LtlFormula (UnaryFormula(StateFormula operand, UnaryFormulaOperator.Globally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
    /// <paramref name="rightOperand" />.
    static member Until (leftOperand : LtlFormula, rightOperand : LtlFormula) =
        Requires.NotNull leftOperand "leftOperand"
        Requires.NotNull rightOperand "rightOperand"

        LtlFormula (BinaryFormula(leftOperand.Formula, BinaryFormulaOperator.Until, rightOperand.Formula))

    /// Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
    /// <paramref name="rightOperand" />.
    static member Until (leftOperand : Expression<Func<bool>>, rightOperand : Expression<Func<bool>>) =
        Requires.NotNull leftOperand "leftOperand"
        Requires.NotNull rightOperand "rightOperand"

        LtlFormula (BinaryFormula(StateFormula leftOperand, BinaryFormulaOperator.Until, StateFormula rightOperand))