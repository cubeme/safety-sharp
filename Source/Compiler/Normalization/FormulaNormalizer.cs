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

namespace SafetySharp.Compiler.Normalization
{
	using System;
	using Analysis;
	using Analysis.Formulas;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Normalizes all implicit conversions from a Boolean expression to a <see cref="LtlFormula" /> or
	///     <see cref="CtlFormula" /> by explicitly invoking the
	///     <see cref="Ltl.StateExpression(System.Linq.Expressions.Expression{System.Func{bool}})" /> or
	///     <see cref="Ctl.StateExpression(System.Linq.Expressions.Expression{System.Func{bool}})" /> methods.
	/// </summary>
	public sealed class FormulaNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     Represents the <see cref="CtlFormula" /> type.
		/// </summary>
		private INamedTypeSymbol _ctlFormulaType;

		/// <summary>
		///     Represents the <see cref="Ctl" /> type.
		/// </summary>
		private INamedTypeSymbol _ctlType;

		/// <summary>
		///     Represents the <see cref="Formula" /> type.
		/// </summary>
		private INamedTypeSymbol _formulaType;

		/// <summary>
		///     Represents the <see cref="LtlFormula" /> type.
		/// </summary>
		private INamedTypeSymbol _ltlFormulaType;

		/// <summary>
		///     Represents the <see cref="Ltl" /> type.
		/// </summary>
		private INamedTypeSymbol _ltlType;

		/// <summary>
		///     Normalizes the syntax trees of the <see cref="Compilation" />.
		/// </summary>
		protected override Compilation Normalize()
		{
			_ctlFormulaType = Compilation.GetTypeSymbol<CtlFormula>();
			_ltlFormulaType = Compilation.GetTypeSymbol<LtlFormula>();
			_ctlType = Compilation.GetTypeSymbol(typeof(Ctl));
			_ltlType = Compilation.GetTypeSymbol(typeof(Ltl));
			_formulaType = Compilation.GetTypeSymbol<Formula>();

			return base.Normalize();
		}

		/// <summary>
		///     Normalizes the <paramref name="binaryExpression" />.
		/// </summary>
		public override SyntaxNode VisitBinaryExpression(BinaryExpressionSyntax binaryExpression)
		{
			var expressionType = DetermineType(binaryExpression);
			if (expressionType == ExpressionType.Other)
				return base.VisitBinaryExpression(binaryExpression);

			var left = ReplaceImplicitConversion(expressionType, binaryExpression.Left);
			var right = ReplaceImplicitConversion(expressionType, binaryExpression.Right);
			return binaryExpression.Update(left, binaryExpression.OperatorToken, right);
		}

		/// <summary>
		///     Normalizes the <paramref name="assignment" />.
		/// </summary>
		public override SyntaxNode VisitAssignmentExpression(AssignmentExpressionSyntax assignment)
		{
			var leftType = DetermineType(assignment.Left);
			if (leftType == ExpressionType.Other)
				return base.VisitAssignmentExpression(assignment);

			var rightType = DetermineType(assignment.Right);
			if (rightType != ExpressionType.Other)
				return base.VisitAssignmentExpression(assignment);

			return assignment.WithRight(CreateInvocation(leftType, assignment.Right));
		}

		/// <summary>
		///     Normalizes the <paramref name="cast" />.
		/// </summary>
		public override SyntaxNode VisitCastExpression(CastExpressionSyntax cast)
		{
			var expressionType = DetermineType(cast);
			if (expressionType == ExpressionType.Other)
				return base.VisitCastExpression(cast);

			return CreateInvocation(expressionType, cast.Expression);
		}

		/// <summary>
		///     Normalizes the <paramref name="declarator" />.
		/// </summary>
		public override SyntaxNode VisitVariableDeclarator(VariableDeclaratorSyntax declarator)
		{
			if (declarator.Initializer == null)
				return base.VisitVariableDeclarator(declarator);

			var variableType = DetermineType(declarator.GetVariableType(SemanticModel));
			if (variableType == ExpressionType.Other)
				return base.VisitVariableDeclarator(declarator);

			var initializerType = DetermineType(declarator.Initializer.Value);
			if (initializerType != ExpressionType.Other)
				return base.VisitVariableDeclarator(declarator);

			var initializer = declarator.Initializer.WithValue(CreateInvocation(variableType, declarator.Initializer.Value));
			return declarator.WithInitializer(initializer);
		}

		/// <summary>
		///     Normalizes the <paramref name="argument" />.
		/// </summary>
		public override SyntaxNode VisitArgument(ArgumentSyntax argument)
		{
			var parameterSymbol = argument.GetParameterSymbol(SemanticModel);
			if (parameterSymbol.RefKind != RefKind.None)
				return base.VisitArgument(argument);

			var parameterType = DetermineType(parameterSymbol.Type);
			if (parameterType == ExpressionType.Other)
				return base.VisitArgument(argument);

			return argument.WithExpression(ReplaceImplicitConversion(parameterType, argument.Expression));
		}

		/// <summary>
		///     Checks whether <paramref name="expression" /> is implicitly converted to <paramref name="targetExpressionType" />. If
		///     so,
		///     replaces the implicit conversion by an invocation of the corresponding state expression factory method.
		/// </summary>
		private ExpressionSyntax ReplaceImplicitConversion(ExpressionType targetExpressionType, ExpressionSyntax expression)
		{
			if (SemanticModel.GetTypeInfo(expression).Type.IsDerivedFrom(_formulaType))
				return (ExpressionSyntax)Visit(expression);

			var conversion = SemanticModel.ClassifyConversion(expression, GetTargetType(targetExpressionType));
			if (conversion.IsUserDefined && conversion.IsImplicit)
				return CreateInvocation(targetExpressionType, (ExpressionSyntax)Visit(expression));

			return (ExpressionSyntax)Visit(expression);
		}

		/// <summary>
		///     Gets the <see cref="INamedTypeSymbol" /> corresponding to the <paramref name="expressionType" />.
		/// </summary>
		private INamedTypeSymbol GetTargetType(ExpressionType expressionType)
		{
			switch (expressionType)
			{
				case ExpressionType.Ctl:
					return _ctlFormulaType;
				case ExpressionType.Ltl:
					return _ltlFormulaType;
				default:
					Assert.NotReached("Unexpected expression type.");
					return null;
			}
		}

		/// <summary>
		///     Creates the invocation of the factory function for the <paramref name="expressionType" /> and
		///     <paramref name="expression" />.
		/// </summary>
		private ExpressionSyntax CreateInvocation(ExpressionType expressionType, ExpressionSyntax expression)
		{
			SyntaxNode type;
			switch (expressionType)
			{
				case ExpressionType.Ctl:
					type = Syntax.TypeExpression(_ctlType);
					break;
				case ExpressionType.Ltl:
					type = Syntax.TypeExpression(_ltlType);
					break;
				default:
					Assert.NotReached("Unexpected expression type.");
					return null;
			}

			var memberAccess = Syntax.MemberAccessExpression(type, Syntax.IdentifierName("StateExpression"));
			var invocation = Syntax.InvocationExpression(memberAccess, expression);
			return (ExpressionSyntax)invocation;
		}

		/// <summary>
		///     Classifies the type of the <paramref name="expression" />.
		/// </summary>
		private ExpressionType DetermineType(ExpressionSyntax expression)
		{
			return DetermineType(SemanticModel.GetTypeInfo(expression).Type);
		}

		/// <summary>
		///     Classifies the type of the <paramref name="expressionType" />.
		/// </summary>
		private ExpressionType DetermineType(ITypeSymbol expressionType)
		{
			if (expressionType.Equals(_ctlFormulaType))
				return ExpressionType.Ctl;

			if (expressionType.Equals(_ltlFormulaType))
				return ExpressionType.Ltl;

			return ExpressionType.Other;
		}

		/// <summary>
		///     Indicates the type of an expression.
		/// </summary>
		private enum ExpressionType
		{
			/// <summary>
			///     Indicates that the expression represents a <see cref="CtlFormula" />.
			/// </summary>
			Ctl,

			/// <summary>
			///     Indicates that the expression represents a <see cref="LtlFormula" />.
			/// </summary>
			Ltl,

			/// <summary>
			///     Indicates that the expression has some other type.
			/// </summary>
			Other
		}
	}
}