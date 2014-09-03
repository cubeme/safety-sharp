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

namespace SafetySharp.CSharpCompiler.Normalization
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Splits multiple local variable declarations declared by the same declaration into mulitple declarations.
	/// 
	///     For instance:
	///     <code>
	///  		int x, y = 3, z;
	///  		// becomes:
	///  		int x; int y = 3; int z;
	/// 	</code>
	/// </summary>
	public class LocalDeclarationNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public LocalDeclarationNormalizer()
			: base(NormalizationScope.ComponentStatements)
		{
		}

		/// <summary>
		///     Normalizes all variable declarations within the <paramref name="block" />.
		/// </summary>
		public override SyntaxNode VisitBlock(BlockSyntax block)
		{
			block = (BlockSyntax)base.VisitBlock(block);
			var statements = block.Statements;

			for (var i = 0; i < statements.Count; ++i)
			{
				var localDeclaration = statements[i] as LocalDeclarationStatementSyntax;
				if (localDeclaration == null || localDeclaration.Declaration.Variables.Count == 1)
					continue;

				statements = statements.RemoveAt(i);

				var count = localDeclaration.Declaration.Variables.Count;
				for (var j = 0; j < count; ++j)
				{
					var declarator = localDeclaration.Declaration.Variables[j];
					var declaration = localDeclaration.Declaration.WithVariables(SyntaxFactory.SingletonSeparatedList(declarator));
					var local = SyntaxFactory.LocalDeclarationStatement(localDeclaration.Modifiers, declaration);

					if (j == 0)
						local = local.WithLeadingTrivia(localDeclaration);
					else
						local = local.WithLeadingSpace();

					if (j == count - 1)
						local = local.WithTrailingTrivia(localDeclaration);

					statements = statements.Insert(i + j, local);
				}
			}

			return block.WithStatements(statements);
		}
	}
}