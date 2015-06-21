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
	using System.Collections.Generic;
	using System.Linq;
	using Utilities;

	/// <summary>
	///     Represents a name scope within which all elements must be uniquely named.
	/// </summary>
	internal class NameScope
	{
		/// <summary>
		///     The list of names that are in use already.
		/// </summary>
		private readonly List<string> _knownNames = new List<string>();

		/// <summary>
		///     Makes <paramref name="name" /> unique within the name scope.
		/// </summary>
		/// <param name="name">The name that should be made unique.</param>
		public string MakeUnique(string name)
		{
			// Check if the name is unique already; in that case, don't change it
			if (!IsUnique(name))
			{
				// Otherwise, append an increasing number to the name until it is unique
				for (var i = 1;; ++i)
				{
					var uniqueName = name + i;
					if (!IsUnique(uniqueName))
						continue;

					name = uniqueName;
					break;
				}
			}

			_knownNames.Add(name);
			return name;
		}

		/// <summary>
		///     Gets a value indicating whether <paramref name="name" /> is unique within the name scope.
		/// </summary>
		/// <param name="name">The name that should be checked.</param>
		public bool IsUnique(string name)
		{
			Requires.NotNullOrWhitespace(name, () => name);

			// ReSharper disable once SimplifyLinqExpression
			return !_knownNames.Any(knownName => knownName == name);
		}
	}
}