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

namespace SafetySharp.Analysis
{
	using System;
	using System.Linq.Expressions;
	using CompilerServices;
	using Formulas;
	using Utilities;

	/// <summary>
	///     Provides factory methods for the construction of computation tree logic formulas.
	/// </summary>
	public static class Ctl
	{
		/// <summary>
		///     Gets a <see cref="OperatorFactory" /> instance that provides methods for the application of CTL operators that
		///     operate on all paths of a subtree of a computation tree.
		/// </summary>
		public static readonly OperatorFactory AllPaths;

		/// <summary>
		///     Gets a <see cref="OperatorFactory" /> instance that provides methods for the application of CTL operators that
		///     require the existence of a certain path within the subtree of a computation tree.
		/// </summary>
		public static readonly OperatorFactory ExistsPath;

		/// <summary>
		///     Initializes the type.
		/// </summary>
		static Ctl()
		{
			AllPaths = new OperatorFactory(PathQuantifier.All);
			ExistsPath = new OperatorFactory(PathQuantifier.Exists);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that evaluates <paramref name="expression" /> within a system state.
		/// </summary>
		/// <param name="expression">The expression that should be evaluated.</param>
		public static CtlFormula StateExpression(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);
			return CSharpTransformation.Transform(expression);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that evaluates <paramref name="expression" /> within a system state.
		/// </summary>
		/// <param name="expression">[LiftExpression] The expression that should be evaluated.</param>
		public static CtlFormula StateExpression([LiftExpression] bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Provides factory methods for CTL operators.
		/// </summary>
		public class OperatorFactory
		{
			/// <summary>
			///     The path quantifier that is used to construct the <see cref="Formula" /> instances.
			/// </summary>
			private readonly PathQuantifier _pathQuantifier;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="pathQuantifier">The path quantifier that should be used to construct the <see cref="Formula" /> instances.</param>
			internal OperatorFactory(PathQuantifier pathQuantifier)
			{
				_pathQuantifier = pathQuantifier;
				Requires.InRange(pathQuantifier, () => pathQuantifier);
			}

			#region Not

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'not' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'not' operator should be applied to.</param>
			public CtlFormula Not(CtlFormula operand)
			{
				Requires.NotNull(operand, () => operand);
				return new UnaryFormula(operand, UnaryFormulaOperator.Not, _pathQuantifier);
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'not' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'not' operator should be applied to.</param>
			public CtlFormula Not(Expression<Func<bool>> operand)
			{
				Requires.NotNull(operand, () => operand);
				return Not(CSharpTransformation.Transform(operand));
			}

			#endregion

			#region Next

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'next' operator should be applied to.</param>
			public CtlFormula Next(CtlFormula operand)
			{
				Requires.NotNull(operand, () => operand);
				return new UnaryFormula(operand, UnaryFormulaOperator.Next, _pathQuantifier);
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'next' operator should be applied to.</param>
			public CtlFormula Next(Expression<Func<bool>> operand)
			{
				Requires.NotNull(operand, () => operand);
				return Next(CSharpTransformation.Transform(operand));
			}

			#endregion

			#region Finally

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
			public CtlFormula Finally(CtlFormula operand)
			{
				Requires.NotNull(operand, () => operand);
				return new UnaryFormula(operand, UnaryFormulaOperator.Finally, _pathQuantifier);
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
			public CtlFormula Finally(Expression<Func<bool>> operand)
			{
				Requires.NotNull(operand, () => operand);
				return Finally(CSharpTransformation.Transform(operand));
			}

			#endregion

			#region Globally

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
			public CtlFormula Globally(CtlFormula operand)
			{
				Requires.NotNull(operand, () => operand);
				return new UnaryFormula(operand, UnaryFormulaOperator.Globally, _pathQuantifier);
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
			public CtlFormula Globally(Expression<Func<bool>> operand)
			{
				Requires.NotNull(operand, () => operand);
				return Globally(CSharpTransformation.Transform(operand));
			}

			#endregion

			#region Until

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until(Expression<Func<bool>> leftOperand, Expression<Func<bool>> rightOperand)
			{
				Requires.NotNull(leftOperand, () => leftOperand);
				Requires.NotNull(rightOperand, () => rightOperand);

				return Until(CSharpTransformation.Transform(leftOperand), CSharpTransformation.Transform(rightOperand));
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until(CtlFormula leftOperand, CtlFormula rightOperand)
			{
				Requires.NotNull(leftOperand, () => leftOperand);
				Requires.NotNull(rightOperand, () => rightOperand);

				return new BinaryFormula(leftOperand, BinaryFormulaOperator.Until, _pathQuantifier, rightOperand);
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until(Expression<Func<bool>> leftOperand, CtlFormula rightOperand)
			{
				Requires.NotNull(leftOperand, () => leftOperand);
				Requires.NotNull(rightOperand, () => rightOperand);

				return Until(CSharpTransformation.Transform(leftOperand), rightOperand);
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until(CtlFormula leftOperand, Expression<Func<bool>> rightOperand)
			{
				Requires.NotNull(leftOperand, () => leftOperand);
				Requires.NotNull(rightOperand, () => rightOperand);

				return Until(leftOperand, CSharpTransformation.Transform(rightOperand));
			}

			#endregion

			#region Unlifted

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'not' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">[LiftExpression] The operand the 'not' operator should be applied to.</param>
			public CtlFormula Not([LiftExpression] bool operand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">[LiftExpression] The operand the 'next' operator should be applied to.</param>
			public CtlFormula Next([LiftExpression] bool operand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">[LiftExpression] The operand the 'finally' operator should be applied to.</param>
			public CtlFormula Finally([LiftExpression] bool operand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
			/// </summary>
			/// <param name="operand">[LiftExpression] The operand the 'globally' operator should be applied to.</param>
			public CtlFormula Globally([LiftExpression] bool operand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until([LiftExpression] bool leftOperand, [LiftExpression] bool rightOperand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until([LiftExpression] bool leftOperand, CtlFormula rightOperand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until(CtlFormula leftOperand, [LiftExpression] bool rightOperand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until([LiftExpression] bool leftOperand, Expression<Func<bool>> rightOperand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			/// <summary>
			///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
			///     <paramref name="rightOperand" />.
			/// </summary>
			/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
			/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
			public CtlFormula Until(Expression<Func<bool>> leftOperand, [LiftExpression] bool rightOperand)
			{
				Requires.CompilationTransformation();
				return null;
			}

			#endregion
		}
	}
}