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

namespace SafetySharp.CSharp.Normalization
{
	using System;
	using System.Linq;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Utilities;

	/// <summary>
	///     <para>
	///         Generates the required calls to the <see cref="Component.SetInitialValues{T}" /> method for all field assignments
	///         within component constructors.
	///         <example>
	///             <code>
	///      				_booleanField = false;
	///      				_integerField = Choose(1, 2, 3, 4);
	///      			</code>
	///             is translated to
	///             <code>
	///      				SetInitialValues(() => _booleanField, true, false);
	///      				SetInitialValues(() => _integerField, true, 1, 2, 3, 4);
	///      			</code>
	///         </example>
	///         That way, we'll always get notified whenever the initial values of a field are changed, regardless of the actual
	///         control flow within the constructor or the constructor chain. It's also possible for a derived type to overwrite the
	///         initial value of a field of a base type.
	///     </para>
	/// 
	///     <para>
	///         Additionally, we have handle field variable initializers within constructors. In accordance with C# 5 §10.11.3 we
	///         add the calls to <see cref="Component.SetInitialValues{T}" /> to the beginning of all constructors with a
	///         constructor initializer that is either empty or <c>base(...)</c>. The actual field initialization, however, is left
	///         unchanged, as we would otherwise change the semantics of the code. Field initializers are executed before the base
	///         constructor is invoked, which cannot be legally expressed in C# and would therefore require MSIL code rewriting. If
	///         we moved the field initializations to the constructors, virtual method calls in base class constructors would
	///         incorrectly observe default values for fields that should have been initialized already.
	///         <example>
	///             <code>
	///    				class C : Component
	///    				{
	///    					bool b = true;
	///   					int i = Choose(1, 2, 3);
	///   					C(int x) : this()
	///   					{
	///   						i = x;
	///   					}
	///   					C()
	///   					{
	/// 							b = false;
	///   					}
	///    				}
	///    			</code>
	///             is translated to
	///             <code>
	///    				class C : Component
	///    				{
	///    					bool b = true;
	///   					int i = Choose(1, 2, 3);
	///   					C(int x) : this() // We're not adding the SetInitialValues calls for the field initializes here
	/// 										  // as that would incorrectly overwrite the value assigned to b by the default constructor
	///   					{ 
	///   						SetInitialValues(() => i, true, x); // Overwrites the previous value of i
	///   					}
	///   					C() // Note that the second parameter is false, as the actual field value has already been set
	///   					{ SetInitialValues(() => b, false, true); SetInitialValues(() => i, false, 1, 2, 3);
	/// 							SetInitialValues(() => b, true, false);
	///   					}
	///    				}
	///    			</code>
	///         </example>
	///     </para>
	/// </summary>
	internal class SetInitialValuesNormalization : CSharpNormalizer
	{
		private bool _inConstructor = false;

		public override SyntaxNode VisitConstructorDeclaration(ConstructorDeclarationSyntax node)
		{
			var classDeclaration = node.Parent as ClassDeclarationSyntax;
			if (classDeclaration == null)
				return node;

			if (!classDeclaration.IsComponentDeclaration(SemanticModel))
				return node;

			_inConstructor = true;
			var newNode = base.VisitConstructorDeclaration(node);
			_inConstructor = false;

			return newNode;
		}

		public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax node)
		{
			if (!_inConstructor)
				return node;

			var expression = node.Expression as BinaryExpressionSyntax;
			if (expression == null || expression.CSharpKind() != SyntaxKind.SimpleAssignmentExpression)
				return node;

			Assert.That(!(expression.Left is BinaryExpressionSyntax), "Unexpected chained assignment.");

			var symbol = SemanticModel.GetSymbolInfo(expression.Left).Symbol as IFieldSymbol;
			if (symbol == null)
				return node;

			var code = String.Format("SetInitialValues(() => {0}, true, {1});", expression.Left, String.Join(", ", GetValues(expression.Right)));

			return SyntaxFactory.ParseStatement(code)
								.WithLeadingTrivia(node.GetLeadingTrivia())
								.WithTrailingTrivia(node.GetTrailingTrivia());
		}

		private object[] GetValues(ExpressionSyntax expression)
		{
			return new object[] { "true", "false" };
		}
	}
}