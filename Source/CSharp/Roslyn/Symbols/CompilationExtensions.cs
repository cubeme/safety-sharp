﻿// The MIT License (MIT)
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

namespace SafetySharp.CSharp.Roslyn.Symbols
{
	using System;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Modeling;
	using Utilities;

	/// <summary>
	///   Provides extension methods for working with <see cref="Compilation" /> instances.
	/// </summary>
	public static class CompilationExtensions
	{
		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol" /> representing <typeparamref name="T" /> within the context of the
		///   <paramref name="compilation" />.
		/// </summary>
		/// <typeparam name="T">The type the symbol should be returned for.</typeparam>
		/// <param name="compilation">The compilation the type symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetTypeSymbol<T>([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);
			return compilation.GetTypeByMetadataName(typeof(T).FullName);
		}

		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol" /> representing <paramref name="type" /> within the context of the
		///   <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the type symbol should be returned for.</param>
		/// <param name="type">The type the symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetTypeSymbol([NotNull] this Compilation compilation, [NotNull] Type type)
		{
			Requires.NotNull(compilation, () => compilation);
			Requires.NotNull(type, () => type);

			return compilation.GetTypeByMetadataName(type.FullName);
		}

		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol" /> representing the type with with name <paramref name="metadataName" /> within
		///   the context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the type symbol should be returned for.</param>
		/// <param name="metadataName">The metadata name of the type the symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetTypeSymbol([NotNull] this Compilation compilation, [NotNull] string metadataName)
		{
			Requires.NotNull(compilation, () => compilation);
			Requires.NotNullOrWhitespace(metadataName, () => metadataName);

			return compilation.GetTypeByMetadataName(metadataName);
		}

		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol " /> representing the <see cref="Component" /> class within the
		///   context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the class symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetComponentClassSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);
			return compilation.GetTypeSymbol<Component>();
		}

		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol " /> representing the <see cref="Fault" /> class within the
		///   context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the class symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetFaultClassSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);
			return compilation.GetTypeSymbol<Fault>();
		}

		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol " /> representing the <see cref="OccurrencePatternAttribute" /> class within the
		///   context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the class symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetOccurrencePatternAttributeSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);
			return compilation.GetTypeSymbol<OccurrencePatternAttribute>();
		}

		/// <summary>
		///   Gets the <see cref="INamedTypeSymbol " /> representing the <see cref="IComponent" /> interface within the
		///   context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the interface symbol should be returned for.</param>
		[Pure, NotNull]
		public static INamedTypeSymbol GetComponentInterfaceSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);
			return compilation.GetTypeSymbol<IComponent>();
		}

		/// <summary>
		///   Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Update()" /> method within the
		///   context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the attribute symbol should be returned for.</param>
		[Pure, NotNull]
		public static IMethodSymbol GetUpdateMethodSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);

			return compilation
				.GetTypeSymbol<Component>()
				.GetMembers("Update")
				.OfType<IMethodSymbol>()
				.Single(method => method.Parameters.Length == 0 && method.ReturnsVoid);
		}

		/// <summary>
		///   Gets the <see cref="IMethodSymbol " /> representing the <see cref="Component.Bind(PortBinding)" /> method within
		///   the context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the attribute symbol should be returned for.</param>
		[Pure, NotNull]
		public static IMethodSymbol GetComponentBindMethodSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);

			return compilation
				.GetTypeSymbol<Component>()
				.GetMembers("Bind")
				.OfType<IMethodSymbol>()
				.Single(method => method.Parameters.Length == 1);
		}

		/// <summary>
		///   Gets the <see cref="IMethodSymbol " /> representing the <see cref="Model.Bind(PortBinding)" /> method
		///   within the context of the <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the attribute symbol should be returned for.</param>
		[Pure, NotNull]
		public static IMethodSymbol GetModelBindMethodSymbol([NotNull] this Compilation compilation)
		{
			Requires.NotNull(compilation, () => compilation);

			return compilation
				.GetTypeSymbol<Model>()
				.GetMembers("Bind")
				.OfType<IMethodSymbol>()
				.Single(method => method.Parameters.Length == 1);
		}
	}
}