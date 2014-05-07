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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Immutable;
	using Metamodel;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Transforms C# object trees into partitions, adding the dynamic parts of a <see cref="Model" /> instance.
	/// </summary>
	internal class PartitionTransformation
	{
		/// <summary>
		///     The model already containing the static parts the partitions are being added to.
		/// </summary>
		private readonly Model _model;

		/// <summary>
		///     Initializes a new instance of the <see cref="PartitionTransformation" /> type.
		/// </summary>
		/// <param name="model">The model already containing the static parts the partitions should be added to.</param>
		internal PartitionTransformation(Model model)
		{
			Argument.NotNull(model, () => model);
			_model = model;
		}

		/// <summary>
		///     Transforms the C# partition root components into partitions, returning a completed <see cref="Model" /> instance with
		///     all static and dynamic parts required for model checking.
		/// </summary>
		/// <param name="partitionRoots">The partition root components that should be added to the model.</param>
		internal Model Transform(ImmutableArray<Component> partitionRoots)
		{
			foreach (var partitionRoot in partitionRoots)
				TransformPartition(partitionRoot);

			return _model;
		}

		/// <summary>
		///     Transforms the <paramref name="partitionRoot" /> and adds it to the model.
		/// </summary>
		/// <param name="partitionRoot">The partition root component that should be added to the model.</param>
		private void TransformPartition(Component partitionRoot)
		{

		}
	}
}