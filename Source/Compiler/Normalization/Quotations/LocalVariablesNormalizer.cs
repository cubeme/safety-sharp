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
	using System.Collections.Generic;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;
	using Runtime;

	/// <summary>
	///     Ensures that all names of local variables are unique within a method's scope, and renames them otherwise.
	/// </summary>
	public sealed class LocalVariablesNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     Maps each local variable to its new name.
		/// </summary>
		private readonly Dictionary<ILocalSymbol, string> _nameMap = new Dictionary<ILocalSymbol, string>();

		/// <summary>
		///     The name scope that is used to generate unique names for the local variables.
		/// </summary>
		private NameScope _nameScope;

		/// <summary>
		///     Indicates if the normalizer is within a method body.
		/// </summary>
		private bool _withinMethod;

		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		public override SyntaxNode VisitMethodDeclaration(MethodDeclarationSyntax methodDeclaration)
		{
			if (!methodDeclaration.GenerateMethodBodyMetadata(SemanticModel))
				return methodDeclaration;

			_withinMethod = true;
			_nameScope = methodDeclaration.GetNameScope(SemanticModel, includeLocals: false);
			methodDeclaration = (MethodDeclarationSyntax)base.VisitMethodDeclaration(methodDeclaration);

			_withinMethod = false;
			return methodDeclaration;
		}

		/// <summary>
		///     Adds the declared <paramref name="variable" /> to the name map and renames it, if necessary.
		/// </summary>
		public override SyntaxNode VisitVariableDeclarator(VariableDeclaratorSyntax variable)
		{
			if (!_withinMethod)
				return variable;

			var symbol = variable.GetDeclaredSymbol<ILocalSymbol>(SemanticModel);
			variable = (VariableDeclaratorSyntax)base.VisitVariableDeclarator(variable);

			if (!_nameMap.ContainsKey(symbol))
				_nameMap.Add(symbol, symbol.Name);

			if (_nameScope.IsUnique(symbol.Name))
			{
				_nameScope.Add(symbol.Name);
				return variable;
			}

			var newName = _nameScope.MakeUnique(symbol.Name);
			_nameMap[symbol] = newName;

			return variable.WithIdentifier(SyntaxFactory.Identifier(newName));
		}

		/// <summary>
		///     Renames the <paramref name="identifier" /> if necessary.
		/// </summary>
		public override SyntaxNode VisitIdentifierName(IdentifierNameSyntax identifier)
		{
			if (!_withinMethod)
				return identifier;

			var symbol = identifier.GetReferencedSymbol(SemanticModel) as ILocalSymbol;
			if (symbol == null)
				return identifier;

			return identifier.WithIdentifier(SyntaxFactory.Identifier(_nameMap[symbol]));
		}
	}
}