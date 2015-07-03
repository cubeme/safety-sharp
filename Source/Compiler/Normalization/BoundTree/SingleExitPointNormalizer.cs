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

namespace SafetySharp.Compiler.Normalization.BoundTree
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Editing;
	using Roslyn.Syntax;
	using Utilities;

	/// <summary>
	///     Ensures that a method only has a single exit point at the end of its body. For instance:
	///     <code>
	///     if (x) return 1;
	///     F();
	///     return 2;
	/// 
	///     // becomes
	/// 
	///     var hasReturned = false;
	///     var returnValue = 0;
	///     if (x) { hasReturned = true; returnValue = 1; }
	///     if (!hasReturned)
	///     { 
	///        F();
	///        hasReturned = true;
	///        returnValue = 2;
	///     } 
	///     return returnValue;
	///     </code>
	/// </summary>
	public sealed class SingleExitPointNormalizer : BoundTreeNormalizer
	{
		/// <summary>
		///     The identifier of the variable indicating that the method has returned.
		/// </summary>
		private IdentifierNameSyntax _hasReturnedVariable;

		/// <summary>
		///     Indicates whether the method returns a value.
		/// </summary>
		private bool _returnsValue;

		/// <summary>
		///     The identifier of the variable storing the return value, if any.
		/// </summary>
		private IdentifierNameSyntax _returnValueVariable;

		/// <summary>
		///     Normalizes the <paramref name="methodDeclaration" />.
		/// </summary>
		protected override SyntaxNode Normalize(MethodDeclarationSyntax methodDeclaration)
		{
			var returnCount = methodDeclaration.Descendants<ReturnStatementSyntax>().Count();

			// If there is no return statement within the method's body, there's nothing to do
			if (returnCount == 0)
				return methodDeclaration;

			// If there is only one return and it is the last method body's last statement, there's nothing to do
			if (returnCount == 1 && methodDeclaration.Body.Statements[methodDeclaration.Body.Statements.Count - 1] is ReturnStatementSyntax)
				return methodDeclaration;

			// Otherwise, we have to normalize the method
			var nameScope = methodDeclaration.GetNameScope(SemanticModel, includeLocals: true);
			var symbol = methodDeclaration.GetMethodSymbol(SemanticModel);

			_returnsValue = !symbol.ReturnsVoid;
			_hasReturnedVariable = SyntaxFactory.IdentifierName(nameScope.MakeUnique("hasReturned"));
			_returnValueVariable = _returnsValue ? SyntaxFactory.IdentifierName(nameScope.MakeUnique("returnValue")) : null;

			var rewriter = new Rewriter(Syntax, _hasReturnedVariable);
			methodDeclaration = (MethodDeclarationSyntax)rewriter.Visit(methodDeclaration);
			methodDeclaration = (MethodDeclarationSyntax)base.Normalize(methodDeclaration);

			// Generate the declarations for the local variables
			var hasReturnedLocal = Syntax.LocalDeclarationStatement(Syntax.TypeExpression<bool>(SemanticModel),
				_hasReturnedVariable.Identifier.ValueText, Syntax.FalseLiteralExpression());
			var statements = methodDeclaration.Body.Statements.Insert(0, (StatementSyntax)hasReturnedLocal);

			if (_returnsValue)
			{
				var returnValueLocal = Syntax.LocalDeclarationStatement(symbol.ReturnType, _returnValueVariable.Identifier.ValueText);
				statements = statements.Insert(0, (StatementSyntax)returnValueLocal);

				// If the method returns a value, add the final return statement, which by now is the only one within the entire method body
				statements = statements.Add((StatementSyntax)Syntax.ReturnStatement(_returnValueVariable));
			}

			return methodDeclaration.WithBody(SyntaxFactory.Block(statements)).NormalizeWhitespace();
		}

		/// <summary>
		///     Replaces the return statement within the block with updates to the return variables.
		/// </summary>
		public override SyntaxNode VisitBlock(BlockSyntax block)
		{
			var returnIndex = ReturnIndex(block.Statements);
			block = (BlockSyntax)base.VisitBlock(block);

			// If the block contains no return statement, we're done
			if (returnIndex == -1)
				return block;

			// Otherwise, update the return values and skip all dead code
			Assert.That(returnIndex == block.Statements.Count - 1, "The return statement must be the last statement of the block.");

			var statements = block.Statements.ToList();
			statements.RemoveAt(statements.Count - 1);

			var setHasReturned = (ExpressionSyntax)Syntax.AssignmentStatement(_hasReturnedVariable, Syntax.TrueLiteralExpression());
			statements.Add((StatementSyntax)Syntax.ExpressionStatement(setHasReturned));

			if (_returnsValue)
			{
				var returnStatement = (ReturnStatementSyntax)block.Statements[returnIndex];
				var setReturnValue = (ExpressionSyntax)Syntax.AssignmentStatement(_returnValueVariable, returnStatement.Expression);
				statements.Add((StatementSyntax)Syntax.ExpressionStatement(setReturnValue));
			}

			return SyntaxFactory.Block(statements);
		}

		/// <summary>
		///     Gets the index of the first return statement within the <paramref name="statements" />.
		/// </summary>
		private static int ReturnIndex(SyntaxList<StatementSyntax> statements)
		{
			for (var i = 0; i < statements.Count; ++i)
			{
				if (statements[i].Kind() == SyntaxKind.ReturnStatement)
					return i;
			}

			return -1;
		}

		/// <summary>
		///     Ensures that code after a return statement is only executed when that return statement has not been taken.
		/// </summary>
		private class Rewriter : CSharpSyntaxRewriter
		{
			/// <summary>
			///     The identifier of the variable indicating that the method has returned.
			/// </summary>
			private readonly IdentifierNameSyntax _hasReturnedVariable;

			/// <summary>
			///     The syntax generator that is used to generate the new method body code.
			/// </summary>
			private readonly SyntaxGenerator _syntax;

			/// <summary>
			///     Indicates whether a set of statement potentially contains a return statement.
			/// </summary>
			private bool _potentiallyReturns;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			public Rewriter(SyntaxGenerator syntax, IdentifierNameSyntax hasReturnedVariable)
			{
				_syntax = syntax;
				_hasReturnedVariable = hasReturnedVariable;
			}

			/// <summary>
			///     Removes all dead code (assumes that there are no gotos) and ensures that statements within the block that follow a
			///     potentially returning one are only executed when the return has not been taken.
			/// </summary>
			public override SyntaxNode VisitBlock(BlockSyntax block)
			{
				var returnIndex = ReturnIndex(block.Statements);
				var liveCode = returnIndex == -1 ? block.Statements : block.Statements.Take(returnIndex + 1);
				var statements = GenerateBlockStatements(liveCode.ToArray());

				return SyntaxFactory.Block(statements);
			}

			/// <summary>
			///     Normalizes the <paramref name="ifStatement" />.
			/// </summary>
			public override SyntaxNode VisitIfStatement(IfStatementSyntax ifStatement)
			{
				_potentiallyReturns = false;
				var thenStatement = (StatementSyntax)Visit(ifStatement.Statement);
				var thenReturns = _potentiallyReturns;

				if (ifStatement.Else == null)
					return _syntax.IfThenElseStatement(ifStatement.Condition, new[] { thenStatement }, null);

				_potentiallyReturns = false;
				var elseStatement = (StatementSyntax)Visit(ifStatement.Else.Statement);
				var elseReturns = _potentiallyReturns;

				_potentiallyReturns = thenReturns || elseReturns;
				return _syntax.IfThenElseStatement(ifStatement.Condition, new[] { thenStatement }, new[] { elseStatement });
			}

			/// <summary>
			///     Generates the individual statements for a block consisting of the <paramref name="statements" />, where each statement
			///     might potentially return and therefore subsequent statements have to be protected by <c>if (!hasReturned) ...</c>.
			/// </summary>
			private IEnumerable<StatementSyntax> GenerateBlockStatements(StatementSyntax[] statements, int offset = 0)
			{
				for (; offset < statements.Length; ++offset)
				{
					_potentiallyReturns = false;

					var transformedStatement = (StatementSyntax)Visit(statements[offset]);
					yield return transformedStatement;

					if (!_potentiallyReturns || offset >= statements.Length - 1)
						continue;

					var condition = (ExpressionSyntax)_syntax.LogicalNotExpression(_hasReturnedVariable);
					yield return _syntax.IfThenElseStatement(condition, GenerateBlockStatements(statements, offset + 1), null);
					yield break;
				}
			}

			/// <summary>
			///     Normalizes the <paramref name="returnStatement" />.
			/// </summary>
			public override SyntaxNode VisitReturnStatement(ReturnStatementSyntax returnStatement)
			{
				_potentiallyReturns = true;
				return returnStatement;
			}
		}
	}
}