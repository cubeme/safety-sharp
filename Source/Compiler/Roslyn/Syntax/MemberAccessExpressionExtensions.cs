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

namespace SafetySharp.Compiler.Roslyn.Syntax
{
	using System;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Symbols;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with <see cref="MemberAccessExpressionSyntax" /> instances.
	/// </summary>
	public static class MemberAccessExpressionExtensions
	{
		/// <summary>
		///     If <paramref name="node" /> is a dynamic member lookup on either <see cref="IComponent.RequiredPorts" />,
		///     <see cref="IComponent.ProvidedPorts" />, <see cref="Component.RequiredPorts" />, or
		///     <see cref="Component.ProvidedPorts" />, returns all declared ports of the target component with the given name.
		/// </summary>
		/// <param name="node">The member access expression that should be analyzed.</param>
		/// <param name="semanticModel">The semantic model that should be used to resolve type information.</param>
		[Pure]
		public static PortCollection GetReferencedPorts([NotNull] this MemberAccessExpressionSyntax node,
														[NotNull] SemanticModel semanticModel)
		{
			Requires.NotNull(node, () => node);
			Requires.NotNull(semanticModel, () => semanticModel);

			var symbol = semanticModel.GetSymbolInfo(node.Expression).Symbol as IPropertySymbol;
			if (symbol == null)
				return null;

			var requiredPortsSymbol = (IPropertySymbol)semanticModel.GetComponentClassSymbol().GetMembers("RequiredPorts").Single();
			var providedPortsSymbol = (IPropertySymbol)semanticModel.GetComponentClassSymbol().GetMembers("ProvidedPorts").Single();

			if (!symbol.Overrides(requiredPortsSymbol) && !symbol.Overrides(providedPortsSymbol))
			{
				requiredPortsSymbol = (IPropertySymbol)semanticModel.GetComponentInterfaceSymbol().GetMembers("RequiredPorts").Single();
				providedPortsSymbol = (IPropertySymbol)semanticModel.GetComponentInterfaceSymbol().GetMembers("ProvidedPorts").Single();

				if (!symbol.Overrides(requiredPortsSymbol) && !symbol.Overrides(providedPortsSymbol))
					return null;
			}

			var portName = node.Name.Identifier.ValueText;
			var isRequiredPort = symbol.Equals(requiredPortsSymbol);
			var nestedMemberAccess = node.Expression.RemoveParentheses() as MemberAccessExpressionSyntax;

			ITypeSymbol targetSymbol = null;
			var nonVirtualInvocation = false;

			if (nestedMemberAccess == null)
				targetSymbol = semanticModel.GetEnclosingSymbol(node.SpanStart).ContainingType;
			else
			{
				var castExpression = nestedMemberAccess.Expression.RemoveParentheses() as CastExpressionSyntax;
				if (castExpression != null)
				{
					targetSymbol = castExpression.Type.GetReferencedSymbol<ITypeSymbol>(semanticModel);

					var uncastSymbol = castExpression.Expression.GetReferencedSymbol(semanticModel) as IParameterSymbol;
					nonVirtualInvocation = uncastSymbol != null && uncastSymbol.IsThis && uncastSymbol.Type.BaseType.Equals(targetSymbol);
				}
				else if (nestedMemberAccess.Expression is BaseExpressionSyntax)
				{
					targetSymbol = semanticModel.GetEnclosingSymbol(node.SpanStart).ContainingType.BaseType;
					nonVirtualInvocation = true;
				}
				else
					targetSymbol = nestedMemberAccess.Expression.GetExpressionType(semanticModel);
			}

			Assert.NotNull(targetSymbol, "Failed to determine the target symbol.");

			var portSymbols = isRequiredPort ? targetSymbol.GetRequiredPorts(semanticModel) : targetSymbol.GetProvidedPorts(semanticModel);
			var ports = portSymbols.Where(p =>
			{
				var propertySymbol = p.AssociatedSymbol as IPropertySymbol;
				return propertySymbol != null ? propertySymbol.Name == portName : p.Name == portName;
			}).ToArray();

			return new PortCollection(targetSymbol, ports, portName, nonVirtualInvocation, isRequiredPort);
		}
	}
}