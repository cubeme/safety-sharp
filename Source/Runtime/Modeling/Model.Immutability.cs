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

namespace SafetySharp.Runtime.Modeling
{
	using System;
	using System.Diagnostics;
	using Utilities;

	partial class Model
	{
		/// <summary>
		///     Indicates whether the models's metadata has been sealed, disallowing any future modifications.
		/// </summary>
		private bool _isSealed;

		/// <summary>
		///     Gets a value indicating whether the metadata has been finalized and any modifications of the metadata are prohibited.
		/// </summary>
		internal bool IsMetadataFinalized
		{
			get { return _isSealed; }
		}

		/// <summary>
		///     Finalizes the models's metadata, disallowing any future metadata modifications.
		/// </summary>
		internal void FinalizeMetadata()
		{
			if (_isSealed)
				return;

			_isSealed = true;
			_synthesizedRoot = new RootComponent(_roots, _bindings);
		}

		/// <summary>
		///     Ensures that the model's metadata has not yet been sealed.
		/// </summary>
		[DebuggerHidden]
		internal void RequiresNotSealed()
		{
			Requires.That(!_isSealed, "Modifications of the model's metadata are only allowed during model initialization.");
		}

		/// <summary>
		///     Ensures that the model's metadata has been sealed.
		/// </summary>
		[DebuggerHidden]
		internal void RequiresIsSealed()
		{
			Requires.That(_isSealed, "Cannot access the model's metadata during model initialization.");
		}
	}
}