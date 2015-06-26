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

namespace SafetySharp.Compiler
{
	using System;
	using System.Collections.Generic;
	using System.Collections.ObjectModel;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Utilities;

	/// <summary>
	///     Represents a set of ports with the same name.
	/// </summary>
	public class PortCollection : Collection<Port>
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="declaringType">The declaring type of the ports.</param>
		/// <param name="portSymbols">The ports contained in the collection.</param>
		/// <param name="name">The common name of the ports contained in the collection.</param>
		/// <param name="nonVirtualInvocation">Indicates whether the ports should be invoked non-virtually.</param>
		/// <param name="containsRequiredPorts">Indicates whether the collection contains required ports.</param>
		public PortCollection([NotNull] ITypeSymbol declaringType, [NotNull] IMethodSymbol[] portSymbols, [NotNull] string name,
							  bool nonVirtualInvocation, bool containsRequiredPorts)
		{
			Requires.NotNull(declaringType, () => declaringType);
			Requires.NotNull(portSymbols, () => portSymbols);
			Requires.NotNullOrWhitespace(name, () => name);

			DeclaringType = declaringType;
			Name = name;
			ContainsRequiredPorts = containsRequiredPorts;
			NonVirtualInvocation = nonVirtualInvocation;

			// We add ports for all property accessors declared by property ports
			foreach (var port in portSymbols)
				Add(new Port(port, port.Name, nonVirtualInvocation, containsRequiredPorts));

			Assert.That(this.All(p => p.IsRequiredPort == containsRequiredPorts),
				"Cannot have required and provided ports in the same collection.");
		}

		/// <summary>
		///     Gets a value indicating whether the ports should be invoked non-virtually.
		/// </summary>
		public bool NonVirtualInvocation { get; private set; }

		/// <summary>
		///     Gets the common name of the ports contained in the collection.
		/// </summary>
		public string Name { get; private set; }

		/// <summary>
		///     Gets the declaring type of the ports.
		/// </summary>
		public ITypeSymbol DeclaringType { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the collection contains required ports.
		/// </summary>
		public bool ContainsRequiredPorts { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the collection contains provided ports.
		/// </summary>
		public bool ContainsProvidedPorts
		{
			get { return !ContainsRequiredPorts; }
		}

		/// <summary>
		///     Removes all inaccessible ports from the collection.
		/// </summary>
		/// <param name="semanticModel">The semantic model that should be used to decide whether a port is accessible.</param>
		/// <param name="location">The location within the document from where the ports should be accessible.</param>
		public void RemoveInaccessiblePorts([NotNull] SemanticModel semanticModel, int location)
		{
			Requires.NotNull(semanticModel, () => semanticModel);

			foreach (var port in this.Where(port => !semanticModel.IsAccessible(location, port.Symbol)).ToArray())
				Remove(port);
		}

		/// <summary>
		///     Tries to find a port that is signature-compatible to <paramref name="methodSymbol" />.
		/// </summary>
		/// <param name="methodSymbol">The method symbol defining the signature the port must be compatible to.</param>
		private IEnumerable<Port> FindOfType([NotNull] IMethodSymbol methodSymbol)
		{
			Requires.NotNull(methodSymbol, () => methodSymbol);
			return this.Where(p => p.IsCompatibleTo(methodSymbol));
		}

		/// <summary>
		///     Filters the port collection so that only ports that are signature-compatible to <paramref name="delegateSymbol" />
		///     remain in the collection.
		/// </summary>
		/// <param name="delegateSymbol">The delegate symbol defining the signature the filtered ports must be compatible to.</param>
		public void Filter([NotNull] INamedTypeSymbol delegateSymbol)
		{
			Requires.NotNull(delegateSymbol, () => delegateSymbol);
			Requires.ArgumentSatisfies(delegateSymbol.TypeKind == TypeKind.Delegate, () => delegateSymbol, "Expected a delegate symbol.");
			Requires.ArgumentSatisfies(delegateSymbol.TypeKind == TypeKind.Delegate, () => delegateSymbol, "Expected a delegate symbol.");

			if (delegateSymbol.DelegateInvokeMethod == null)
				return;

			foreach (var port in this.Where(port => !port.IsCompatibleTo(delegateSymbol.DelegateInvokeMethod)).ToArray())
				Remove(port);
		}

		/// <summary>
		///     Gets a set of possible port bindings.
		/// </summary>
		/// <param name="other">The other collection of ports the binding candidates should be returned for.</param>
		[NotNull]
		public BindingCandidate[] GetBindingCandidates([NotNull] PortCollection other)
		{
			return this
				.SelectMany(port => other.FindOfType(port.Symbol).Select(p => new BindingCandidate { Left = port, Right = p }))
				.Where(candidate => candidate.Right != null)
				.ToArray();
		}

		/// <summary>
		///     Represents a candidate for a port binding.
		/// </summary>
		public struct BindingCandidate
		{
			/// <summary>
			///     The port on the left-hand side of the binding.
			/// </summary>
			public Port Left;

			/// <summary>
			///     The port on the right-hand side of the binding.
			/// </summary>
			public Port Right;
		}
	}
}