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

namespace Tests.Execution
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.Globalization;
	using System.IO;
	using System.Linq;
	using System.Reflection;
	using JetBrains.Annotations;
	using SafetySharp.Modeling;
	using SafetySharp.Utilities;
	using Shouldly;
	using Utilities;
	using Xunit.Abstractions;

	[AttributeUsage(AttributeTargets.Method, Inherited = false, AllowMultiple = false)]
	public sealed class TestAttribute : Attribute
	{
		private static readonly Random _random = new Random();
		private readonly int _testCount;

		public TestAttribute(int testCount)
		{
			_testCount = testCount;
		}

		public void ExecuteTests(TestTraceOutput output, Component originalComponent, Component transformedComponent,
								 MethodInfo originalMethod, MethodInfo transformedMethod)
		{
			var parameters = originalMethod.GetParameters();
			var originalArguments = new object[parameters.Length];
			var transformedArguments = new object[parameters.Length];
			var valueFactories = new Func<object>[parameters.Length];

			for (var i = 0; i < parameters.Length; ++i)
			{
				if (parameters[i].ParameterType == typeof(int) || parameters[i].ParameterType == typeof(int).MakeByRefType())
					valueFactories[i] = RandomInt32;
				else if (parameters[i].ParameterType == typeof(double) || parameters[i].ParameterType == typeof(double).MakeByRefType())
					valueFactories[i] = RandomDouble;
				else if (parameters[i].ParameterType == typeof(bool) || parameters[i].ParameterType == typeof(bool).MakeByRefType())
					valueFactories[i] = RandomBoolean;
				else
					Assert.NotReached("Unknown parameter type '{0}'.", parameters[i].ParameterType);
			}

			output.Log("Testing '{0}'", originalMethod);
			for (var i = 0; i < _testCount; ++i)
			{
				output.Trace("----- Inputs -----");
				for (var j = 0; j < originalArguments.Length; ++j)
				{
					originalArguments[j] = valueFactories[j]();
					transformedArguments[j] = originalArguments[j];

					output.Trace("{0} = {1}", parameters[j].Name, originalArguments[j]);
				}

				var originalResult = originalMethod.Invoke(originalComponent, originalArguments);
				var transformedResult = transformedMethod.Invoke(transformedComponent, transformedArguments);

				if (originalResult != null && originalResult.GetType().IsEnum)
				{
					originalResult = ((IConvertible)originalResult).ToInt32(CultureInfo.InvariantCulture);
					transformedResult = ((IConvertible)transformedResult).ToInt32(CultureInfo.InvariantCulture);
				}

				transformedResult.ShouldBe(originalResult);
				transformedArguments.ShouldBe(originalArguments);

				for (var j = 0; j < originalComponent.Metadata.Fields.Length; ++j)
				{
					var originalField = originalComponent.Metadata.Fields[j];
					output.Trace("Comparing field '{0}'", originalField.FieldInfo);

					var transformedField = transformedComponent.Metadata.Fields.Single(f => f.Name == originalField.Name);
					transformedField.FieldInfo.GetValue(transformedComponent).ShouldBe(originalField.FieldInfo.GetValue(originalComponent));
				}
			}
		}

		private static object RandomInt32()
		{
			return _random.Next(-200, 200);
		}

		private static object RandomBoolean()
		{
			return _random.Next() % 2 == 0;
		}

		private static object RandomDouble()
		{
			return _random.NextDouble() * 100.0 - 50.0;
		}
	}

	public class SemanticEqualityComponent : TestComponent
	{
		private Component CreateTransformedComponent()
		{
			var serializer = new CSharpSerializer();
			var code = serializer.Serialize(Metadata);

			Output.Log("==========================================");
			Output.Log("Transformed Code");
			Output.Log("==========================================");
			Output.Log("{0}", code);

			var compilation = Tests.CreateCompilation(code);
			Tests.CheckForSafetySharpDiagnostics(compilation);
			var assembly = Tests.CompileSafetySharp(compilation, Output);

			var componentType = assembly.GetTypes().First(type => typeof(Component).IsAssignableFrom(type));
			return (Component)Activator.CreateInstance(componentType);
		}

		protected override void Check()
		{
			var methods = (from method in GetType().GetMethods()
						   let attribute = method.GetCustomAttribute<TestAttribute>()
						   where attribute != null
						   select new { Method = method, Attribute = attribute }).ToArray();

			if (methods.Length == 0)
				throw new TestException("Unable to find any methods that should be tested.");

			var originalComponent = this;
			var transformedComponent = CreateTransformedComponent();
			transformedComponent.MetadataBuilder.FinalizeMetadata("C");

			foreach (var methodInfo in methods)
			{
				var originalMethod = methodInfo.Method;
				var transformedMethod = transformedComponent.GetType().GetMethods().Single(m => m.Name == originalMethod.Name);
				methodInfo.Attribute.ExecuteTests(Output, originalComponent, transformedComponent, originalMethod, transformedMethod);
			}
		}
	}

	partial class ExecutionTests
	{
		public ExecutionTests(ITestOutputHelper output)
			: base(output)
		{
		}

		[UsedImplicitly]
		public static IEnumerable<object[]> DiscoverTests(string directory)
		{
			return EnumerateTestCases(Path.Combine(Path.GetDirectoryName(GetFileName()), directory));
		}
	}
}