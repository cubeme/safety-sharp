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

namespace SafetySharp.Simulation
{
	using System;
	using Modeling;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Provides extension methods for simulating <see cref="Model" /> instances.
	/// </summary>
	internal static class ModelExtensions
	{
		/// <summary>
		///     Executes a simulation step of the <paramref name="model" />.
		/// </summary>
		/// <param name="model">The model that should be executed.</param>
		// TODO: Respect explicit component scheduling
		internal static void ExecuteStep(this Model model)
		{
			Requires.NotNull(model, () => model);
			model.GetMetadata().RootComponent.VisitPreOrder(metadata => metadata.Component.Update());
		}

		/// <summary>
		///     Resets the model to its initial state.
		/// </summary>
		/// <param name="model">The model that should be reset.</param>
		internal static void Reset(this Model model)
		{
			Requires.NotNull(model, () => model);
			model.GetMetadata().RootComponent.VisitPreOrder(metadata => metadata.Component.Reset());
		}
	}
}