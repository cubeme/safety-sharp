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

namespace SafetySharp.Modeling
{
	using System;
	using System.Diagnostics;
	using System.Reflection;
	using Utilities;

	partial class Component
	{
		/// <summary>
		///     Indicates whether the component's metadata has been sealed, disallowing any future modifications.
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
		///     Finalizes the component's metadata, disallowing any future metadata modifications.
		/// </summary>
		/// <param name="parent">The parent component of the component.</param>
		/// <param name="name">The name of the component.</param>
		/// <param name="slot">
		///     The slot of the component, i.e., the zero-based index within the parent component's subcomponent list.
		/// </param>
		/// <param name="field">The field of the parent component that stores the component instance.</param>
		internal void FinalizeMetadata(Component parent = null, string name = "", int slot = -1, FieldInfo field = null)
		{
			if (_isSealed)
				return;

			_isSealed = true;
			_parent = parent;
			_name = name;
			_slot = slot;
			_parentField = field;

			InitializeFields();
			InitializeBindings();
			InitializeSubcomponents();
			InitializeFaults();
		}

		/// <summary>
		///     Ensures that the component's metadata has not yet been sealed.
		/// </summary>
		[DebuggerHidden]
		internal void RequiresNotSealed()
		{
			Requires.That(!_isSealed, "Modifications of the component's metadata are only allowed during model initialization.");
		}

		/// <summary>
		///     Ensures that the component's metadata has been sealed.
		/// </summary>
		[DebuggerHidden]
		internal void RequiresIsSealed()
		{
			Requires.That(_isSealed, "Cannot access the component's metadata during model initialization.");
		}
	}
}