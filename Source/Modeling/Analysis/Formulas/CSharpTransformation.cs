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

namespace SafetySharp.Analysis.Formulas
{
	using System;
	using System.Linq;
	using System.Linq.Expressions;
	using System.Reflection;
	using CompilerServices;
	using Modeling;
	using Runtime.Expressions;
	using Utilities;
	using BinaryExpression = System.Linq.Expressions.BinaryExpression;
	using Expression = Runtime.Expressions.Expression;
	using UnaryExpression = System.Linq.Expressions.UnaryExpression;

	/// <summary>
	///     Transforms an <see cref="Expression{TDelegate}" /> to a <see cref="StateFormula" />.
	/// </summary>
	internal class CSharpTransformation : ExpressionVisitor
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		private CSharpTransformation()
		{
		}

		/// <summary>
		///     Gets the transformed <see cref="Runtime.Expressions.Expression" />.
		/// </summary>
		public Expression Expression { get; private set; }

		/// <summary>
		///     Transforms the <paramref name="expression" />, returning the transformed <see cref="Runtime.Expressions.Expression" />.
		/// </summary>
		/// <param name="expression">The expression that should be transformed.</param>
		private Expression Transform(System.Linq.Expressions.Expression expression)
		{
			Visit(expression);
			return Expression;
		}

		/// <summary>
		///     Transforms the <paramref name="expression" /> to a <see cref="StateFormula" />.
		/// </summary>
		/// <param name="expression"></param>
		public static StateFormula Transform(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);

			return new StateFormula(new Lazy<Expression>(() =>
			{
				var transformation = new CSharpTransformation();
				transformation.Visit(expression.Body);
				return transformation.Expression;
			}));
		}

		/// <summary>
		///     Converts the constant <paramref name="value" /> to an <see cref="Expression" />.
		/// </summary>
		/// <param name="value">The value that should be converted.</param>
		private void ConvertConstant(object value)
		{
			if (value is int)
				Expression = new IntegerLiteralExpression((int)value);
			else if (value is double)
				Expression = new DoubleLiteralExpression((double)value);
			else if (value is bool)
				Expression = new BooleanLiteralExpression((bool)value);
			else if (value.GetType().IsEnum)
				Expression = new EnumerationLiteralExpression(value);
			else
				Assert.NotReached("Unsupported constant value type: {0}.", value.GetType().FullName);
		}

		/// <summary>
		///     Visits the <see cref="ConstantExpression" />.
		/// </summary>
		protected override System.Linq.Expressions.Expression VisitConstant(ConstantExpression node)
		{
			ConvertConstant(node.Value);
			return node;
		}

		/// <summary>
		///     Visits the children of the <see cref="System.Linq.Expressions.UnaryExpression" />.
		/// </summary>
		protected override System.Linq.Expressions.Expression VisitUnary(UnaryExpression node)
		{
			node = (UnaryExpression)base.VisitUnary(node);
			var operand = Transform(node.Operand);

			switch (node.NodeType)
			{
				case ExpressionType.Negate:
					Expression = new Runtime.Expressions.UnaryExpression(UnaryOperator.Minus, operand);
					break;
				case ExpressionType.UnaryPlus:
					Expression = operand;
					break;
				case ExpressionType.Not:
					Expression = new Runtime.Expressions.UnaryExpression(UnaryOperator.Not, operand);
					break;
				case ExpressionType.Convert:
					// We'll skip over 'enum literal to int' conversions
					if (!node.Operand.Type.IsEnum)
						goto default;
					break;
				default:
					Assert.NotReached("Unsupported unary operator '{0}'.", node.NodeType);
					break;
			}

			return node;
		}

		/// <summary>
		///     Visits the children of the <see cref="System.Linq.Expressions.BinaryExpression" />.
		/// </summary>
		protected override System.Linq.Expressions.Expression VisitBinary(BinaryExpression node)
		{
			node = (BinaryExpression)base.VisitBinary(node);
			var leftOperand = Transform(node.Left);
			var rightOperand = Transform(node.Right);
			var binaryOperator = BinaryOperator.Add;

			switch (node.NodeType)
			{
				case ExpressionType.Add:
					binaryOperator = BinaryOperator.Add;
					break;
				case ExpressionType.Subtract:
					binaryOperator = BinaryOperator.Subtract;
					break;
				case ExpressionType.Multiply:
					binaryOperator = BinaryOperator.Multiply;
					break;
				case ExpressionType.Divide:
					binaryOperator = BinaryOperator.Divide;
					break;
				case ExpressionType.Modulo:
					binaryOperator = BinaryOperator.Modulo;
					break;
				case ExpressionType.And:
				case ExpressionType.AndAlso:
					binaryOperator = BinaryOperator.And;
					break;
				case ExpressionType.Or:
				case ExpressionType.OrElse:
					binaryOperator = BinaryOperator.Or;
					break;
				case ExpressionType.Equal:
					binaryOperator = BinaryOperator.Equals;
					break;
				case ExpressionType.NotEqual:
					binaryOperator = BinaryOperator.NotEquals;
					break;
				case ExpressionType.GreaterThan:
					binaryOperator = BinaryOperator.Greater;
					break;
				case ExpressionType.GreaterThanOrEqual:
					binaryOperator = BinaryOperator.GreaterEqual;
					break;
				case ExpressionType.LessThan:
					binaryOperator = BinaryOperator.Less;
					break;
				case ExpressionType.LessThanOrEqual:
					binaryOperator = BinaryOperator.LessEqual;
					break;
				default:
					Assert.NotReached("Unsupported binary operator '{0}'.", node.NodeType);
					break;
			}

			Expression = new Runtime.Expressions.BinaryExpression(binaryOperator, leftOperand, rightOperand);
			return node;
		}

		/// <summary>
		///     Gets the CLR object represented by the <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression the value should be returned for.</param>
		private static object GetValue(System.Linq.Expressions.Expression expression)
		{
			var constant = expression as ConstantExpression;
			if (constant != null)
				return constant.Value;

			var memberExpression = expression as MemberExpression;
			if (memberExpression != null)
			{
				var obj = GetValue(memberExpression.Expression);
				var field = memberExpression.Member as FieldInfo;

				if (field != null)
					return field.GetValue(obj);

				var property = memberExpression.Member as PropertyInfo;
				if (property != null && property.CanRead)
					return property.GetValue(obj);

				Assert.NotReached("Invalid member access: '{0}'.", expression);
			}

			Assert.NotReached("Invalid expression type while trying to retrieve member value: '{0}'.", expression.NodeType);
			return null;
		}

		/// <summary>
		///     Visits the children of the <see cref="MethodCallExpression" />.
		/// </summary>
		protected override System.Linq.Expressions.Expression VisitMethodCall(MethodCallExpression node)
		{
			var component = (IComponent)GetValue(node.Object);
			var arguments = node.Arguments.Select(argument => new ArgumentExpression(Transform(argument), RefKind.None)).ToArray();
			Expression = new MethodInvocationExpression(ReflectionHelpers.GetMethodMetadata(component, node.Method, true), arguments);

			return node;
		}

		/// <summary>
		///     Visits the children of the <see cref="MemberExpression" />.
		/// </summary>
		protected override System.Linq.Expressions.Expression VisitMember(MemberExpression node)
		{
			if (typeof(IComponent).IsAssignableFrom(node.Expression.Type))
			{
				var component = (IComponent)GetValue(node.Expression);
				var field = node.Member as FieldInfo;
				var property = node.Member as PropertyInfo;

				if (field != null)
					Expression = new FieldExpression(ReflectionHelpers.GetFieldMetadata(component, field));
				else if (property != null)
					Expression = new MethodInvocationExpression(ReflectionHelpers.GetMethodMetadata(component, property.GetMethod, true));
				else
					Assert.NotReached("Invalid component member access: '{0}'.", node);
			}
			else if (node.Expression.Type.IsEnum)
			{
				var fieldInfo = (FieldInfo)node.Member;
				Expression = new EnumerationLiteralExpression(fieldInfo.GetValue(null));
			}
			else if (node.Member is FieldInfo)
				ConvertConstant(GetValue(node));

			return node;
		}
	}
}