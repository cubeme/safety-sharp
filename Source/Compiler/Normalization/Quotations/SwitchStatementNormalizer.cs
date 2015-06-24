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

namespace SafetySharp.Compiler.Normalization.Quotations
{
	using System;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn.Syntax;
	using Runtime;

	/// <summary>
	///     Replaces <c>switch</c> statements with the corresponding <c>if</c> statement.
	/// </summary>
	public sealed class SwitchStatementNormalizer : QuotationNormalizer
	{
		/// <summary>
		///     The name scope that is used to generate unique names for the switch expression.
		/// </summary>
		private NameScope _nameScope;

		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		protected override SyntaxNode Normalize(MethodDeclarationSyntax methodDeclaration)
		{
			_nameScope = methodDeclaration.GetNameScope(SemanticModel, includeLocals: true);
			return base.Normalize(methodDeclaration).NormalizeWhitespace();
		}

		/// <summary>
		///     Normalizes the switch statement.
		/// </summary>
		public override SyntaxNode VisitSwitchStatement(SwitchStatementSyntax switchStatement)
		{
			var name = _nameScope.MakeUnique("switchExpr");
			var identifier = Syntax.IdentifierName(name);
			var type = ModelExtensions.GetTypeInfo(SemanticModel, switchStatement.Expression).Type;
			var variable = Syntax.LocalDeclarationStatement(type, name, switchStatement.Expression);

			var sections = switchStatement.Sections;
			var defaultCaseIndex = sections.IndexOf(section => section.Labels.Any(label => label.Keyword.Kind() == SyntaxKind.DefaultKeyword));
			var defaultSection = defaultCaseIndex == -1 ? null : sections[defaultCaseIndex];

			if (defaultCaseIndex != -1)
				sections = sections.RemoveAt(defaultCaseIndex);

			SyntaxNode statement = null;
			for (var i = sections.Count; i > 0; --i)
			{
				var values = sections[i - 1].Labels.Cast<CaseSwitchLabelSyntax>().Select(label => label.Value).ToArray();
				var expression = Syntax.ValueEqualsExpression(identifier, values[0]);

				foreach (var value in values.Skip(1))
					expression = Syntax.LogicalOrExpression(expression, Syntax.ValueEqualsExpression(identifier, value));

				var condition = (ExpressionSyntax)expression;
				if (i == sections.Count && defaultCaseIndex != -1)
					statement = Syntax.IfThenElseStatement(condition, sections[i - 1].Statements, defaultSection.Statements);
				else if (i == sections.Count)
					statement = Syntax.IfThenElseStatement(condition, sections[i - 1].Statements, null);
				else
					statement = Syntax.IfThenElseStatement(condition, sections[i - 1].Statements, new[] { (StatementSyntax)statement });
			}

			if (sections.Count == 0 && defaultCaseIndex == -1)
				statement = SyntaxFactory.EmptyStatement();
			else if (sections.Count == 0 && defaultCaseIndex != -1)
				statement = SyntaxFactory.Block(defaultSection.Statements);

			return SyntaxFactory.Block((StatementSyntax)variable, (StatementSyntax)statement);
		}
	}
}