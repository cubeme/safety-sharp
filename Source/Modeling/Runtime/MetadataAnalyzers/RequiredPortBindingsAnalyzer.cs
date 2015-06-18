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
	using System.Linq;

	/// <summary>
	///     Checks whether there is exactly one binding for all required ports.
	/// </summary>
	internal class RequiredPortBindingsAnalyzer : ModelAnalyzer
	{
		/// <summary>
		///     Analyzes the model's <paramref name="metadata" />.
		/// </summary>
		/// <param name="metadata">The metadata of the model that should be analyzed.</param>
		public override void Analyze(ModelMetadata metadata)
		{
			metadata.RootComponent.VisitPreOrder(component =>
			{
				foreach (var requiredPort in component.RequiredPorts)
				{
					var count = requiredPort.BoundProvidedPorts.Count();

					if (count == 0)
						throw new UnboundRequiredPortException(requiredPort);

					if (count > 1)
						throw new AmbiguousBindingsException(requiredPort);
				}
			});
		}
	}
}