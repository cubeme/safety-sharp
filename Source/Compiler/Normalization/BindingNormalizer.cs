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
	using System.Collections.Generic;
	using System.Linq;
	using System.Runtime.CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;
	using Runtime.Modeling;

	/// <summary>
	///     Replaces all port binding assignments with constructor invocations of <see cref="PortBinding" />.
	/// 
	///     For instance:
	///     <code>
	///    		Bind(c.RequiredPorts.X, ProvidedPorts.Y);
	///    		// becomes (for some matching delegate type D):
	///  		Bind(new PortBinding(PortInfo.RequiredPort((D)c.X, "..."), PortInfo.ProvidedPort((D)Y)));
	///   	</code>
	/// </summary>
	public sealed class BindingNormalizer : Normalizer
	{
		/// <summary>
		///     Represents the [CompilerGenerated] attribute syntax.
		/// </summary>
		private static readonly AttributeListSyntax CompilerGeneratedAttribute =
			SyntaxBuilder.Attribute(typeof(CompilerGeneratedAttribute).FullName).WithTrailingSpace();

		/// <summary>
		///     The delegate types used by the bindings of a component.
		/// </summary>
		private readonly List<DelegateDeclarationSyntax> _delegates = new List<DelegateDeclarationSyntax>();

		/// <summary>
		///     The number of bindings established in the compilation.
		/// </summary>
		private int _bindingCount;

		/// <summary>
		///     Normalizes the <paramref name="classDeclaration" />.
		/// </summary>
		public override SyntaxNode VisitClassDeclaration(ClassDeclarationSyntax classDeclaration)
		{
			var normalizedClassDeclaration = (ClassDeclarationSyntax)base.VisitClassDeclaration(classDeclaration);

			var delegates = _delegates.Select(d => (MemberDeclarationSyntax)d.AddAttributeLists(CompilerGeneratedAttribute)).ToArray();
			_delegates.Clear();

			if (delegates.Length > 0)
				AddCompilationUnit(classDeclaration.GeneratePartWithMembers(SemanticModel, delegates));

			return normalizedClassDeclaration;
		}

		/// <summary>
		///     Normalizes <paramref name="expression" /> if it is an invocation of <see cref="Component.Bind" /> or
		///     <see cref="Model.Bind" />.
		/// </summary>
		public override SyntaxNode VisitInvocationExpression(InvocationExpressionSyntax expression)
		{
			var newExpression = (InvocationExpressionSyntax)base.VisitInvocationExpression(expression);

			// If the expression has changed, that means we're looking at an invocation of the Delayed() function;
			// there's no need to rewrite it.
			if (newExpression != expression)
				return newExpression;

			var methodSymbol = SemanticModel.GetSymbolInfo(expression.Expression).Symbol as IMethodSymbol;
			if (methodSymbol == null)
				return expression;

			var componentBindSymbol = SemanticModel.GetComponentBindMethodSymbol();
			var modelBindSymbol = SemanticModel.GetModelBindMethodSymbol();

			if (!methodSymbol.Equals(componentBindSymbol) && !methodSymbol.Equals(modelBindSymbol))
				return expression;

			// We now know that the argument of the invocation is a port binding in the form of an assignment
			var assignment = (AssignmentExpressionSyntax)expression.ArgumentList.Arguments[0].Expression.RemoveParentheses();
			var leftExpression = (MemberAccessExpressionSyntax)assignment.Left.RemoveParentheses();
			var rightExpression = assignment.Right.RemoveParentheses() as MemberAccessExpressionSyntax;

			// On the right-hand side, we could also have a cast to a delegate type
			CastExpressionSyntax castExpression = null;
			if (rightExpression == null)
			{
				castExpression = (CastExpressionSyntax)assignment.Right.RemoveParentheses();
				rightExpression = (MemberAccessExpressionSyntax)castExpression.Expression.RemoveParentheses();
			}

			var leftPorts = leftExpression.GetReferencedPorts(SemanticModel);
			var rightPorts = rightExpression.GetReferencedPorts(SemanticModel);

			leftPorts.RemoveInaccessiblePorts(SemanticModel, expression.SpanStart);
			rightPorts.RemoveInaccessiblePorts(SemanticModel, expression.SpanStart);

			// If there is a cast, filter the right-hand port list
			if (castExpression != null)
				rightPorts.Filter(castExpression.Type.GetReferencedSymbol<INamedTypeSymbol>(SemanticModel));

			var boundPorts = leftPorts.GetBindingCandidates(rightPorts)[0];
			var delegateName = IdentifierNameSynthesizer.ToSynthesizedName("BindingDelegate" + _bindingCount++);
			var delegateType = boundPorts.Left.Symbol.GetSynthesizedDelegateDeclaration(delegateName);
			_delegates.Add(delegateType);

			var leftPort = CreatePortInfoExpression(boundPorts.Left, leftExpression, delegateType.Identifier.ValueText);
			var rightPort = CreatePortInfoExpression(boundPorts.Right, rightExpression, delegateType.Identifier.ValueText);

			var leftArgument = SyntaxFactory.Argument(leftPort);
			var rightArgument = SyntaxFactory.Argument(rightPort);
			var constructorArgumentList = SyntaxFactory.ArgumentList(SyntaxFactory.SeparatedList(new[] { leftArgument, rightArgument }));
			var portBindingType = SyntaxFactory.ParseTypeName(typeof(PortBinding).FullName);
			var instantiation = SyntaxFactory.ObjectCreationExpression(portBindingType, constructorArgumentList, null);
			var instantiationArgument = SyntaxFactory.Argument(instantiation);

			var argumentList = SyntaxFactory.ArgumentList(SyntaxFactory.SingletonSeparatedList(instantiationArgument));
			return expression.WithArgumentList(argumentList).NormalizeWhitespace().WithTrivia(expression).EnsureSameLineCount(expression);
		}

		/// <summary>
		///     Creates an expression that instantiates a <see cref="PortInfo" /> instance for the given port.
		/// </summary>
		/// <param name="port">The port the expression should be created for.</param>
		/// <param name="portExpression">The port expression that was used to reference the port.</param>
		/// <param name="delegateType">The type of the delegate the port should be cast to.</param>
		private static ExpressionSyntax CreatePortInfoExpression(Port port, MemberAccessExpressionSyntax portExpression, string delegateType)
		{
			// TODO: property ports

			var nestedMemberAccess = portExpression.Expression.RemoveParentheses() as MemberAccessExpressionSyntax;
			var castTarget =
				nestedMemberAccess != null
					? SyntaxFactory.MemberAccessExpression(SyntaxKind.SimpleMemberAccessExpression, nestedMemberAccess.Expression, portExpression.Name)
					: (ExpressionSyntax)portExpression.Name;
			var type = SyntaxFactory.ParseTypeName(delegateType);
			var castExpression = SyntaxFactory.CastExpression(type, SyntaxFactory.ParenthesizedExpression(castTarget)).NormalizeWhitespace();
			var castArgument = SyntaxFactory.Argument(castExpression);
			var arguments = SyntaxFactory.ArgumentList(SyntaxFactory.SingletonSeparatedList(castArgument));
			var portInfoType = SyntaxFactory.ParseTypeName(typeof(PortInfo).FullName);
			var methodName = SyntaxFactory.IdentifierName("MethodPort");
			var memberAccess = SyntaxFactory.MemberAccessExpression(SyntaxKind.SimpleMemberAccessExpression, portInfoType, methodName);
			return SyntaxFactory.InvocationExpression(memberAccess, arguments);
		}
	}
}