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

namespace SafetySharp.CSharp
{
	using System;
	using Metamodel;
	using Metamodel.Expressions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	internal partial class TransformationVisitor
	{
		public override MetamodelElement VisitBinaryExpression(BinaryExpressionSyntax node)
		{
			var left = (Expression)Visit(node.Left);
			var right = (Expression)Visit(node.Right);

			return new BinaryExpression(left, MapBinaryOperator(node.CSharpKind()), right);
		}

		public override MetamodelElement VisitLiteralExpression(LiteralExpressionSyntax node)
		{
			switch (node.Token.CSharpKind())
			{
				case SyntaxKind.TrueKeyword:
					return BooleanLiteral.True;
				case SyntaxKind.FalseKeyword:
					return BooleanLiteral.False;
				case SyntaxKind.NumericLiteralToken:
					if (node.Token.Value is int)
						return new IntegerLiteral((int)node.Token.Value);

					Assert.NotReached("Numeric literals of type '{0}' are not supported.", node.Token.Value.GetType().FullName);
					return null;
				default:
					Assert.NotReached("Unsupported C# literal: '{0}'.", node.Token.CSharpKind());
					return null;
			}
		}

		private static BinaryOperator MapBinaryOperator(SyntaxKind syntaxKind)
		{
			switch (syntaxKind)
			{
				case SyntaxKind.AddExpression:
					return BinaryOperator.Add;
				case SyntaxKind.LogicalAndExpression:
					return BinaryOperator.And;
				default:
					Assert.NotReached("Unsupported C# operator: '{0}'.", syntaxKind);
					return 0;
			}
		}
	}
}