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
[<AllowNullLiteral>]
type LtlFormula internal (formula : CSharpFormula) = 
    /// Gets the wrapped C# formula.
    member internal this.Formula = formula

    /// Applies the implication operator to this instance and the given formula.
    member this.Implies (formula : LtlFormula) = 
        LtlFormula (CSharpBinaryFormula(this.Formula, BinaryFormulaOperator.Implication, formula.Formula))

/// Provides factory methods for the construction of linear temporal logic formulas.
[<AbstractClass; Sealed>]
type Ltl =

    /// Returns a <see cref="LtlFormula" /> that evaluates <paramref name="expression"/> within a system state.
    static member StateExpression (expression : Expression<Func<bool>>) =
        nullArg expression "expression"
        LtlFormula (CSharpStateFormula expression)

    /// Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
    static member Next (operand : LtlFormula) =
        nullArg operand "operand"
        LtlFormula (CSharpUnaryFormula(operand.Formula, UnaryFormulaOperator.Next))

    /// Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
    static member Next (operand : Expression<Func<bool>>) =
        nullArg operand "operand"
        LtlFormula (CSharpUnaryFormula(CSharpStateFormula operand, UnaryFormulaOperator.Next))

    /// Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
    static member Finally (operand : LtlFormula) =
        nullArg operand "operand"
        LtlFormula (CSharpUnaryFormula(operand.Formula, UnaryFormulaOperator.Finally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
    static member Finally (operand : Expression<Func<bool>>) =
        nullArg operand "operand"
        LtlFormula (CSharpUnaryFormula(CSharpStateFormula operand, UnaryFormulaOperator.Finally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
    static member Globally (operand : LtlFormula) =
        nullArg operand "operand"
        LtlFormula (CSharpUnaryFormula(operand.Formula, UnaryFormulaOperator.Globally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
    static member Globally (operand : Expression<Func<bool>>) =
        nullArg operand "operand"
        LtlFormula (CSharpUnaryFormula(CSharpStateFormula operand, UnaryFormulaOperator.Globally))

    /// Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
    /// <paramref name="rightOperand" />.
    static member Until (leftOperand : LtlFormula, rightOperand : LtlFormula) =
        nullArg leftOperand "leftOperand"
        nullArg rightOperand "rightOperand"

        LtlFormula (CSharpBinaryFormula(leftOperand.Formula, BinaryFormulaOperator.Until, rightOperand.Formula))

    /// Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
    /// <paramref name="rightOperand" />.
    static member Until (leftOperand : Expression<Func<bool>>, rightOperand : Expression<Func<bool>>) =
        nullArg leftOperand "leftOperand"
        nullArg rightOperand "rightOperand"

        LtlFormula (CSharpBinaryFormula(CSharpStateFormula leftOperand, BinaryFormulaOperator.Until, CSharpStateFormula rightOperand))

    /// Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
    /// <paramref name="rightOperand" />.
    static member Until (leftOperand : LtlFormula, rightOperand : Expression<Func<bool>>) =
        nullArg leftOperand "leftOperand"
        nullArg rightOperand "rightOperand"

        LtlFormula (CSharpBinaryFormula(leftOperand.Formula, BinaryFormulaOperator.Until, CSharpStateFormula rightOperand))

    /// Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
    /// <paramref name="rightOperand" />.
    static member Until (leftOperand : Expression<Func<bool>>, rightOperand : LtlFormula) =
        nullArg leftOperand "leftOperand"
        nullArg rightOperand "rightOperand"

        LtlFormula (CSharpBinaryFormula(CSharpStateFormula leftOperand, BinaryFormulaOperator.Until, rightOperand.Formula))