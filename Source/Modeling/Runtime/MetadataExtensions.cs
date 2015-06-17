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
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides extension methods for working with S# metadata.
	/// </summary>
	public static class MetadataExtensions
	{
		/// <summary>
		///     Gets the <typeparamref name="TMetadata" /> instance for the <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object the <typeparamref name="TMetadata" /> instance should be retrieved for.</param>
		/// <remarks>
		///     S# users call this method to retrieve the metadata of a S# metadata object. Since this is usually not needed when
		///     modeling components, the <see cref="MetadataObject{TMetadata,TMetadataBuilder}.Metadata" /> property is <c>internal</c>
		///     so as to not clutter up IntelliSense too much.
		/// </remarks>
		public static TMetadata GetMetadata<TMetadata, TMetadataBuilder>(this MetadataObject<TMetadata, TMetadataBuilder> obj)
			where TMetadata : ObjectMetadata
			where TMetadataBuilder : class
		{
			Requires.NotNull(obj, () => obj);
			return obj.Metadata;
		}

		/// <summary>
		///     Gets the <see cref="ObjectMetadata" /> instance for the <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object the <see cref="ObjectMetadata" /> instance should be retrieved for.</param>
		/// <remarks>
		///     S# users call this method to retrieve the metadata of a S# metadata object. Since this is usually not needed when
		///     modeling components, the <see cref="IMetadataObject.Metadata" /> property is implemented explicitly
		///     so as to not clutter up IntelliSense too much.
		/// </remarks>
		public static ObjectMetadata GetMetadata(this IMetadataObject obj)
		{
			Requires.NotNull(obj, () => obj);
			return obj.Metadata;
		}
	}
}