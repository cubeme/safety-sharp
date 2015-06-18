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

namespace SafetySharp.CompilerServices
{
	using System;
	using Modeling;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Provides access to the metadata builders of <see cref="MetadataObject{TMetadata,TMetadataBuilder}" /> instances.
	/// </summary>
	public static class MetadataBuilders
	{
		/// <summary>
		///     Gets the <paramref name="obj" />'s <typeparamref name="TMetadataBuilder" /> if its metadata has not yet been
		///     initialized.
		/// </summary>
		/// <param name="obj">The object the builder should be returned for.</param>
		public static TMetadataBuilder GetBuilder<TMetadata, TMetadataBuilder>(MetadataObject<TMetadata, TMetadataBuilder> obj)
			where TMetadata : ObjectMetadata
			where TMetadataBuilder : class
		{
			return obj.MetadataBuilder;
		}

		/// <summary>
		///     Gets the <paramref name="component" />'s <see cref="ComponentMetadata.Builder" /> if its metadata has not yet
		///     been initialized.
		/// </summary>
		/// <param name="component">The component the builder should be returned for.</param>
		public static ComponentMetadata.Builder GetBuilder(IComponent component)
		{
			Requires.NotNull(component, () => component);
			Requires.OfType<Component>(component, () => component);

			return ((Component)component).MetadataBuilder;
		}

		/// <summary>
		///     Gets the <paramref name="component" />'s <see cref="ComponentMetadata.Builder" /> if its metadata has not yet
		///     been initialized.
		/// </summary>
		/// <param name="component">The component the builder should be returned for.</param>
		public static ComponentMetadata.Builder GetBuilder(Component component)
		{
			Requires.NotNull(component, () => component);
			return component.MetadataBuilder;
		}
	}
}