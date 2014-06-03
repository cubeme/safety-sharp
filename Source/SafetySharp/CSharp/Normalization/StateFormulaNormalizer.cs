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
	using System.Collections.Generic;
	using Extensions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;

	/// <summary>
	///     Rewrites all parameters of method calls with the <see cref="StateFormulaAttribute" />. For instance,
	///     <c>Ltl.Globally(c.Value == 7)</c> is rewritten to <c>Ltl.Globally(Ltl.StateFormula("{0}.Value == 7", c))</c>.
	/// </summary>
	internal class StateFormulaNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Returns the node unmodified, as the <see cref="StateFormulaAttribute" /> is not supported in constructors.
		/// </summary>
		/// <param name="node">The object creation expression that should be visited.</param>
		public override SyntaxNode VisitObjectCreationExpression(ObjectCreationExpressionSyntax node)
		{
			return node;
		}

		/// <summary>
		///     Rewrites the argument if the underlying method parameter has the <see cref="StateFormulaAttribute" /> applied.
		/// </summary>
		/// <param name="node">The node that should be rewritten.</param>
		public override SyntaxNode VisitArgument(ArgumentSyntax node)
		{
			var requiresRewrite = node.ParameterHasAttribute<StateFormulaAttribute>(SemanticModel);
			node = (ArgumentSyntax)base.VisitArgument(node);

			if (!requiresRewrite)
				return node;

			var memberAccesses = GetMemberAccesses(node);
			var formatString = ToFormatString(node, memberAccesses);
			var formatArguments = String.Join(", ", memberAccesses);

			var className = node.GetMethodSymbol(SemanticModel).ContainingSymbol.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
			var expressionString = String.Format("{0}.StateFormula(\"{1}\", new object[] {{ {2} }})", className, formatString, formatArguments);
			var expression = SyntaxFactory.ParseExpression(expressionString);

			return SyntaxFactory.Argument(expression);
		}

		/// <summary>
		///     Generates the format string for the state formula denoted by <paramref name="argument" />.
		/// </summary>
		/// <param name="argument">The argument representing the state formula.</param>
		/// <param name="memberAccesses">The member accesses within <paramref name="argument" />.</param>
		private static string ToFormatString(ArgumentSyntax argument, IEnumerable<ExpressionSyntax> memberAccesses)
		{
			var offset = argument.FullSpan.Start;
			var argumentString = argument.ToFullString();

			var index = 0;
			foreach (var memberAccess in memberAccesses)
			{
				var start = memberAccess.Span.Start - offset;
				var end = memberAccess.Span.End - offset;
				var length = end - start;
				var formatArg = String.Format("{{{0}}}", index);

				offset += length - formatArg.Length;
				++index;

				argumentString = argumentString.Remove(start, end - start);
				argumentString = argumentString.Insert(start, formatArg);
			}

			return argumentString;
		}

		/// <summary>
		///     Gets the members accessed by the state formula <paramref name="argument" />.
		/// </summary>
		/// <param name="argument">The argument representing the state formula.</param>
		private IEnumerable<ExpressionSyntax> GetMemberAccesses(ArgumentSyntax argument)
		{
			var walker = new MemberAccessCollector(SemanticModel);
			walker.Visit(argument);

			return walker.MemberAccesses;
		}

		/// <summary>
		///     Collects member accesses of a C# expression.
		/// </summary>
		private class MemberAccessCollector : CSharpSyntaxWalker
		{
			/// <summary>
			///     The cached symbol of the <see cref="IComponent" /> interface.
			/// </summary>
			private readonly ITypeSymbol _componentInterfaceSymbol;

			/// <summary>
			///     The semantic model that is used to resolve types.
			/// </summary>
			private readonly SemanticModel _semanticModel;

			/// <summary>
			///     Initializes a new instance of the <see cref="MemberAccessCollector" /> type.
			/// </summary>
			/// <param name="semanticModel">The semantic model that should be used to resolve types.</param>
			public MemberAccessCollector(SemanticModel semanticModel)
			{
				MemberAccesses = new List<ExpressionSyntax>();

				_semanticModel = semanticModel;
				_componentInterfaceSymbol = _semanticModel.GetComponentInterfaceSymbol();
			}

			/// <summary>
			///     Gets the expression representing members accessed by the state formula.
			/// </summary>
			public List<ExpressionSyntax> MemberAccesses { get; private set; }

			/// <summary>
			///     Collects a member access that is accessed with a <see cref="MemberAccessExpressionSyntax" />. If the accessed object is
			///     a <see cref="IComponent" /> instance, the last member access is not reported as it should remain in the state formula.
			/// </summary>
			/// <param name="node">The member access that should be collected</param>
			public override void VisitMemberAccessExpression(MemberAccessExpressionSyntax node)
			{
				var typeInfo = _semanticModel.GetTypeInfo(node.Expression);
				if (typeInfo.ConvertedType.IsDerivedFrom(_componentInterfaceSymbol))
					MemberAccesses.Add(node.Expression);
				else
					MemberAccesses.Add(node);
			}

			/// <summary>
			///     Collects a member access that is not part of a <see cref="MemberAccessExpressionSyntax" />.
			/// </summary>
			/// <param name="node">The identifier that should be collected.</param>
			public override void VisitIdentifierName(IdentifierNameSyntax node)
			{
				MemberAccesses.Add(node);
			}
		}
	}
}