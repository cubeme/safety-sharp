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

namespace Tests.Runtime
{
	using System;
	using System.Collections.Generic;
	using System.IO;
	using System.Linq;
	using System.Reflection;
	using System.Text;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using SafetySharp.Compiler.Roslyn.Syntax;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Utilities;
	using Xunit.Abstractions;

	public abstract class TestComponent : Component
	{
		protected ComponentInfo Metadata { get; private set; }

		protected ComponentInfo.Builder Builder
		{
			get { return MetadataBuilders.GetBuilder(this); }
		}

		protected MethodInfo ComponentUpdatedMethod
		{
			get { return typeof(Component).GetMethod("Update"); }
		}

		public void Check(ComponentInfo metadata)
		{
			Metadata = metadata;
			Check();
		}

		protected abstract void Check();

		protected void CheckField(Type fieldType, string fieldName, params object[] initialValues)
		{
			var hasField = Metadata.Fields.Any(field =>
				field.Type == fieldType &&
				field.Name == fieldName &&
				field.Component.Component == this &&
				field.InitialValues.SequenceEqual(initialValues));

			if (hasField)
				return;

			var builder = new StringBuilder();
			builder.AppendLine("Actual Fields:");
			builder.AppendLine("==============");

			foreach (var field in Metadata.Fields)
				builder.AppendLine(field.ToString());

			builder.AppendLine();
			builder.AppendLine("Expected Field:");
			builder.AppendLine("===============");
			builder.AppendFormat("{0} {1} = {2}\n", fieldType.FullName, fieldName, String.Join(", ", initialValues));

			throw new TestException(builder.ToString());
		}

		protected void CheckFault(Fault fault)
		{
			var hasFault = Metadata.Faults.Any(f =>
				f.Component.Component == this &&
				f.Fault == fault);

			if (hasFault)
				return;

			var builder = new StringBuilder();
			builder.AppendLine("Actual Faults:");
			builder.AppendLine("==============");

			//foreach (var f in Metadata.Faults)
			//	builder.AppendFormat("{0} {1} = {2}\n", field.Type.FullName, field.Name, String.Join(", ", field.InitialValues));

			builder.AppendLine();
			builder.AppendLine("Expected Faults:");
			builder.AppendLine("===============");
			//builder.AppendFormat("{0} {1} = {2}\n", fieldType.FullName, fieldName, String.Join(", ", initialValues));

			throw new TestException(builder.ToString());
		}
	}

	partial class RuntimeTests
	{
		public RuntimeTests(ITestOutputHelper output)
			: base(output)
		{
		}

		private void Check(SyntaxTree syntaxTree)
		{
			var compilation = CreateCompilation(syntaxTree);
			var semanticModel = compilation.GetSemanticModel(syntaxTree);

			var componentTypes = syntaxTree
				.Descendants<ClassDeclarationSyntax>()
				.Select(declaration => declaration.GetTypeSymbol(semanticModel))
				.Where(symbol => !symbol.IsGenericType && !symbol.IsAbstract && symbol.ContainingType == null)
				.Select(symbol => symbol.ToDisplayString())
				.ToArray();

			if (componentTypes.Length == 0)
				throw new TestException("Unable to find any testable class declarations.");

			var assembly = CompileSafetySharp(compilation);

			foreach (var componentType in componentTypes)
			{
				var type = assembly.GetType(componentType);
				var component = (TestComponent)Activator.CreateInstance(type);
				var info = MetadataProvider.ComponentBuilders[component].RegisterMetadata();
				component.Check(info);
			}
		}

		[UsedImplicitly]
		public static IEnumerable<object[]> DiscoverTests(string directory)
		{
			return EnumerateTestCases(Path.Combine(Path.GetDirectoryName(GetFileName()), directory));
		}
	}
}