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

namespace SafetySharp.Runtime
{
	using System;
	using System.Reflection;
	using Modeling;
	using Transformation;
	using Utilities;

	/// <summary>
	///     Represents the the immutable metadata of a S# step method.
	/// </summary>
	public sealed class StepMethodMetadata : MethodMetadata
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="stepMethod">The CLR method the metadata should be provided for.</param>
		/// <param name="baseStepMethod">The overridden base step method, if any.</param>
		internal StepMethodMetadata(IMetadataObject obj, MethodInfo stepMethod, MethodMetadata baseStepMethod = null)
			: base(obj, stepMethod, baseMethod: baseStepMethod)
		{
			Requires.That(HasImplementation, () => stepMethod, "Step methods must have an implementation.");
			Requires.That(!(obj is Component) || CanBeAffectedByFaultEffects, () => stepMethod,
				"Step methods of components must be sensitive to fault effects.");
		}

		/// <summary>
		///     Initializes the method's <see cref="MethodBodyMetadata" />.
		/// </summary>
		protected override MethodBodyMetadata InitializeMethodBody()
		{
			// We have to inline all base calls, if any
			var methodBody = base.InitializeMethodBody();
			return MethodInliner.Inline(methodBody, method => BaseMethod == method);
		}
	}
}