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
	using System.Linq;
	using System.Runtime.CompilerServices;
	using CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all port binding assignments with constructor invocations of <see cref="PortBinding" />.
	/// 
	///     For instance:
	///     <code>
	///    		Bind(c.RequiredPorts.X, ProvidedPorts.Y);
	///    		// becomes (for some matching delegate type D):
	///  		MetadataBuilders.GetBuilder(this).Bind(new PortBinding(PortInfo.RequiredPort((D)c.X, "..."), PortInfo.ProvidedPort((D)Y)));
	///   	</code>
	/// </summary>
	public sealed class BindingNormalizer : SyntaxNormalizer
	{
		/// <summary>
		///     The number of bindings established in the compilation.
		/// </summary>
		private int _bindingCount;

		/// <summary>
		///     Represents the [CompilerGenerated] attribute syntax.
		/// </summary>
		private AttributeListSyntax _compilerGeneratedAttribute;

		/// <summary>
		///     The number of bindings established in the compilation.
		/// </summary>
		private int _synthesizedMethodsCount;

		/// <summary>
		///     Normalizes the syntax trees of the <see cref="Compilation" />.
		/// </summary>
		protected override Compilation Normalize()
		{
			_compilerGeneratedAttribute = (AttributeListSyntax)Syntax.Attribute(typeof(CompilerGeneratedAttribute).FullName);
			return base.Normalize();
		}

		/// <summary>
		///     Normalizes the <paramref name="statement" /> if it is an invocation of <see cref="Component.Bind" /> or
		///     <see cref="Model.Bind" />.
		/// </summary>
		public override SyntaxNode VisitExpressionStatement(ExpressionStatementSyntax statement)
		{
			var invocationExpression = statement.Expression as InvocationExpressionSyntax;
			if (invocationExpression == null)
				return base.VisitExpressionStatement(statement);

			var methodSymbol = SemanticModel.GetSymbolInfo(invocationExpression.Expression).Symbol as IMethodSymbol;
			if (methodSymbol == null)
				return statement;

			var componentBindSymbol = SemanticModel.GetComponentBindMethodSymbol();
			var modelBindSymbol = SemanticModel.GetModelBindMethodSymbol();

			if (!methodSymbol.Equals(componentBindSymbol) && !methodSymbol.Equals(modelBindSymbol))
				return statement;

			// We now know that the argument of the invocation is a port binding in the form of an assignment
			var declaringType = SemanticModel.GetEnclosingSymbol(invocationExpression.SpanStart).ContainingType;
			var assignment = (AssignmentExpressionSyntax)invocationExpression.ArgumentList.Arguments[0].Expression.RemoveParentheses();
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

			leftPorts.RemoveInaccessiblePorts(SemanticModel, invocationExpression.SpanStart);
			rightPorts.RemoveInaccessiblePorts(SemanticModel, invocationExpression.SpanStart);

			// If there is a cast, filter the right-hand port list
			if (castExpression != null)
				rightPorts.Filter(castExpression.Type.GetReferencedSymbol<INamedTypeSymbol>(SemanticModel));

			var boundPorts = leftPorts.GetBindingCandidates(rightPorts)[0];
			var delegateName = ("BindingDelegate" + _bindingCount++).ToSynthesized();
			var delegateType = boundPorts.Left.Symbol.GetSynthesizedDelegateDeclaration(delegateName);
			delegateType = delegateType.AddAttributeLists(_compilerGeneratedAttribute);
			AddMembers(declaringType, delegateType);

			var leftPort = CreatePortExpression(declaringType, boundPorts.Left, leftExpression, delegateType.Identifier.ValueText);
			var rightPort = CreatePortExpression(declaringType, boundPorts.Right, rightExpression, delegateType.Identifier.ValueText);

			// MetadataBuilders.GetBuilder(target)
			var metadataBuilderType = Syntax.TypeExpression(SemanticModel.GetTypeSymbol(typeof(MetadataBuilders)));
			var getBuilderMethod = Syntax.MemberAccessExpression(metadataBuilderType, "GetBuilder");
			var invokedMemberExpression = invocationExpression.Expression as MemberAccessExpressionSyntax;
			var builderTarget = invokedMemberExpression == null ? Syntax.ThisExpression() : invokedMemberExpression.Expression.RemoveTrivia();
			var getBuilder = Syntax.InvocationExpression(getBuilderMethod, builderTarget);

			// .WithBinding(leftPort, rightPort)
			var withBindingMethod = Syntax.MemberAccessExpression(getBuilder, "WithBinding");
			var withBinding = Syntax.InvocationExpression(withBindingMethod, leftPort, rightPort);

			return Syntax.ExpressionStatement(withBinding.NormalizeWhitespace()).EnsureLineCount(statement);
		}

		/// <summary>
		///     Creates an expression that instantiates a delegate for the given port.
		/// </summary>
		/// <param name="type">The type that declares the binding.</param>
		/// <param name="port">The port the expression should be created for.</param>
		/// <param name="portExpression">The port expression that was used to reference the port.</param>
		/// <param name="delegateType">The type of the delegate the port should be cast to.</param>
		private ExpressionSyntax CreatePortExpression(INamedTypeSymbol type, Port port, MemberAccessExpressionSyntax portExpression,
													  string delegateType)
		{
			// TODO: property ports

			var portName = port.Symbol.Name;
			string declaringType;
			if (port.NonVirtualInvocation)
			{
				portName = SynthesizePortMethod(type, port, portExpression);
				declaringType = SemanticModel
					.GetEnclosingSymbol(portExpression.SpanStart)
					.ContainingType
					.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
			}
			else
				declaringType = port.Symbol.ContainingType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);

			// Delegate.CreateDelegate(...)
			var delegateClass = Syntax.TypeExpression(Compilation.GetTypeSymbol<Delegate>());
			var createDelegateMethod = Syntax.MemberAccessExpression(delegateClass, "CreateDelegate");

			// Arguments (typeof(delegateType), targetObject, reflectedMethod)
			var typeofDelegate = SyntaxFactory.TypeOfExpression(SyntaxFactory.ParseTypeName(delegateType));
			var reflectedMethod = port.Symbol.GetRuntimeMethodExpression(Syntax, portName, declaringType);
			var nestedMemberAccess = portExpression.Expression.RemoveParentheses() as MemberAccessExpressionSyntax;

			SyntaxNode targetObject;
			if (nestedMemberAccess != null && nestedMemberAccess.Expression is BaseExpressionSyntax)
			{
				if (!port.NonVirtualInvocation)
				{
					var typeSymbol = nestedMemberAccess.Expression.GetReferencedSymbol<IParameterSymbol>(SemanticModel).Type.BaseType;
					targetObject = Syntax.CastExpression(typeSymbol, Syntax.ThisExpression());
				}
				else
					targetObject = Syntax.ThisExpression();
			}
			else if (nestedMemberAccess != null)
				targetObject = nestedMemberAccess.Expression;
			else
				targetObject = Syntax.ThisExpression();

			return (ExpressionSyntax)Syntax.InvocationExpression(createDelegateMethod, typeofDelegate, targetObject, reflectedMethod);
		}

		/// <summary>
		///     Synthesized a method for the <paramref name="port" />.
		/// </summary>
		/// <param name="type">The type that declares the binding.</param>
		/// <param name="port">The port the method should be synthesized for.</param>
		/// <param name="portExpression">The port expression that was used to reference the port.</param>
		private string SynthesizePortMethod(INamedTypeSymbol type, Port port, MemberAccessExpressionSyntax portExpression)
		{
			var portMember = Syntax.MemberAccessExpression(Syntax.BaseExpression(), port.Symbol.Name);
			var parameters = port.Symbol.Parameters.Select(p => Syntax.Argument(p.RefKind, Syntax.IdentifierName(p.Name)));
			var invocation = Syntax.InvocationExpression(portMember, parameters);

			var body = port.Symbol.ReturnsVoid
				? Syntax.ExpressionStatement(invocation)
				: Syntax.ReturnStatement(invocation);

			var method = (MethodDeclarationSyntax)Syntax.MethodDeclaration(
				name: ("SynthesizedPort" + _synthesizedMethodsCount).ToSynthesized(),
				parameters: port.Symbol.Parameters.Select(p => Syntax.ParameterDeclaration(p)),
				typeParameters: port.Symbol.TypeParameters.Select(t => t.Name),
				returnType: Syntax.TypeExpression(port.Symbol.ReturnType),
				accessibility: Accessibility.Private,
				statements: new[] { body });

			var providedAttribute = Syntax.Attribute(Syntax.TypeExpression(Compilation.GetTypeSymbol<ProvidedAttribute>()));
			var compilerGeneratedAttribute = Syntax.Attribute(Syntax.TypeExpression(Compilation.GetTypeSymbol<CompilerGeneratedAttribute>()));

			method = (MethodDeclarationSyntax)Syntax.AddAttributes(method, providedAttribute, compilerGeneratedAttribute);

			AddMembers(type, method);
			++_synthesizedMethodsCount;

			return method.Identifier.ValueText;
		}
	}
}