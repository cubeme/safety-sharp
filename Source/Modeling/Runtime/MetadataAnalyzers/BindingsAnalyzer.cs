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

namespace SafetySharp.Runtime.MetadataAnalyzers
{
	using System;

	/// <summary>
	///     Checks whether there are any invalid bindings. Bindings are invalid when they reference a port of a component that is
	///     not a direct or indirect subcomponent of the component initializing the binding.
	/// </summary>
	internal class BindingsAnalyzer : ModelAnalyzer
	{
		/// <summary>
		///     Analyzes the model's <paramref name="metadata" />.
		/// </summary>
		/// <param name="metadata">The metadata of the model that should be analyzed.</param>
		public override void Analyze(ModelMetadata metadata)
		{
			metadata.RootComponent.VisitPreOrder(component =>
			{
				foreach (var binding in component.Bindings)
				{
					var requiredPortOk = IsSubcomponent(binding.RequiredPort.DeclaringObject, binding.DeclaringComponent);
					var providedPortOk = IsSubcomponent(binding.ProvidedPort.DeclaringObject, binding.DeclaringComponent);

					if (!requiredPortOk || !providedPortOk)
						throw new InvalidBindingException(binding);
				}
			});
		}

		/// <summary>
		///     Checks whether <paramref name="component" /> is direct or indirect subcomponent of <paramref name="parentComponent" />.
		/// </summary>
		/// <param name="component">The component that should be checked.</param>
		/// <param name="parentComponent">The parent component that should be checked.</param>
		private static bool IsSubcomponent(ComponentMetadata component, ComponentMetadata parentComponent)
		{
			var root = parentComponent.RootComponent;
			while (true)
			{
				if (component == parentComponent)
					return true;

				if (component == root)
					return false;

				component = component.ParentComponent;
			}
		}
	}
}