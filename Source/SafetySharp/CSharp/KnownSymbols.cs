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

namespace SafetySharp.CSharp
{
	using System;
	using System.Linq;
	using Metamodel;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Modeling;

	/// <summary>
	///     Contains known symbols for certain C# classes, methods, etc.
	/// </summary>
	internal static class KnownSymbols
	{
		/// <summary>
		///     Initializes the type.
		/// </summary>
		static KnownSymbols()
		{
			var compilation = CSharpCompilation
				.Create("AssemblyMetadata")
				.AddReferences(new MetadataFileReference(typeof(object).Assembly.Location))
				.AddReferences(new MetadataFileReference(typeof(MetamodelElement).Assembly.Location));

			Component = compilation.GetTypeByMetadataName(typeof(Component).FullName);
			UpdateMethod = Component.GetMembers("Update").OfType<IMethodSymbol>().Single();

			var chooseMethods = Component.GetMembers("Choose").OfType<IMethodSymbol>().ToArray();
			ChooseEnumerationLiteralMethod = chooseMethods.Single(method => method.Parameters.Length == 0);
			ChooseFromValuesMethod = chooseMethods.Single(method => method.Parameters.Length != 0);

			var chooseRangeMethods = Component.GetMembers("ChooseFromRange").OfType<IMethodSymbol>().ToArray();
			ChooseFromIntegerRangeMethod = chooseRangeMethods.Single(method => method.Parameters[0].Type.SpecialType == SpecialType.System_Int32);
			ChooseFromDecimalRangeMethod = chooseRangeMethods.Single(method => method.Parameters[0].Type.SpecialType == SpecialType.System_Decimal);
		}

		/// <summary>
		///     Gets the <see cref="ITypeSymbol " /> representing the <see cref="SafetySharp.Modeling.Component" /> class.
		/// </summary>
		public static ITypeSymbol Component { get; private set; }

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the <see cref="SafetySharp.Modeling.Component.Update()" /> method.
		/// </summary>
		public static IMethodSymbol UpdateMethod { get; private set; }

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the <see cref="SafetySharp.Modeling.Component.Choose{T}()" />
		///     method.
		/// </summary>
		public static IMethodSymbol ChooseEnumerationLiteralMethod { get; private set; }

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the
		///     <see cref="SafetySharp.Modeling.Component.Choose{T}(T, T, T[])" /> method.
		/// </summary>
		public static IMethodSymbol ChooseFromValuesMethod { get; private set; }

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the
		///     <see cref="SafetySharp.Modeling.Component.ChooseFromRange(int, int)" /> method.
		/// </summary>
		public static IMethodSymbol ChooseFromIntegerRangeMethod { get; private set; }

		/// <summary>
		///     Gets the <see cref="IMethodSymbol " /> representing the
		///     <see cref="SafetySharp.Modeling.Component.ChooseFromRange(decimal, decimal)" /> method.
		/// </summary>
		public static IMethodSymbol ChooseFromDecimalRangeMethod { get; private set; }
	}
}