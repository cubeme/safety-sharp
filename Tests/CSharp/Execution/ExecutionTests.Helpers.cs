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
		public FieldInfo[] Fields;

		public TestAttribute(int testCount)
		{
			_testCount = testCount;
		}

		public void ExecuteTests(object originalObject, object transformedObject, MethodInfo originalMethod, MethodInfo transformedMethod)
		{
			var parameters = originalMethod.GetParameters();
			var originalArguments = new object[parameters.Length];
			var transformedArguments = new object[parameters.Length];
			var valueFactories = new Func<object>[parameters.Length];
			Fields = originalObject.GetType().GetFields(BindingFlags.Public | BindingFlags.FlattenHierarchy | BindingFlags.Instance);

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

			for (var i = 0; i < _testCount; ++i)
			{
				for (var j = 0; j < originalArguments.Length; ++j)
				{
					originalArguments[j] = valueFactories[j]();
					transformedArguments[j] = originalArguments[j];
				}

				var originalResult = originalMethod.Invoke(originalObject, originalArguments);
				var transformedResult = transformedMethod.Invoke(transformedObject, transformedArguments);

				transformedResult.ShouldBe(originalResult);
				transformedArguments.ShouldBe(originalArguments);

				foreach (var field in Fields)
					field.GetValue(transformedObject).ShouldBe(field.GetValue(originalObject));
			}
		}

		private static object RandomInt32()
		{
			return _random.Next() - _random.Next();
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
		private object CreateTransformedComponent()
		{
			var serializer = new CSharpSerializer();
			var code = serializer.Serialize(Metadata);

			TestOutput.WriteLine("==========================================");
			TestOutput.WriteLine("Serialized Metadata");
			TestOutput.WriteLine("==========================================");
			TestOutput.WriteLine("{0}", code);

			var compilation = Tests.CreateCompilation(code);
			Tests.CheckForSafetySharpDiagnostics(compilation);
			var assembly = Tests.CompileSafetySharp(compilation, TestOutput);

			var componentType = assembly.GetTypes().Single(type => typeof(Component).IsAssignableFrom(type));
			return Activator.CreateInstance(componentType);
		}

		protected override void Check()
		{
			var methods = (from method in GetType().GetMethods()
						   let attribute = method.GetCustomAttribute<TestAttribute>()
						   where attribute != null
						   select new { Method = method, Attribute = attribute }).ToArray();

			if (methods.Length == 0)
				throw new TestException("Unable to find any methods that should be tested.");

			var originalObj = this;
			var transformedObj = CreateTransformedComponent();

			foreach (var methodInfo in methods)
			{
				var originalMethod = methodInfo.Method;
				var transformedMethod = transformedObj
					.GetType().GetMethods()
					.Single(m => m.Name == originalMethod.Name &&
								 m.ReturnType == originalMethod.ReturnType &&
								 m.GetParameters().Select(p => p.ParameterType).SequenceEqual(originalMethod.GetParameters().Select(p => p.ParameterType)));

				methodInfo.Attribute.ExecuteTests(originalObj, transformedObj, originalMethod, transformedMethod);
			}

			foreach (var field in methods[0].Attribute.Fields)
				Log("Tested field: {0}", field);
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