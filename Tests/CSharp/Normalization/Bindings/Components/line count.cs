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

namespace Tests.Normalization.Bindings.Components
{
	using System;
	using SafetySharp.Modeling;

	[CheckTrivia(TriviaType.DocCommentsAndDirectives)]
	partial class In13 : Component
	{
		private In13 i;

		private In13()
		{
			Bind(i
			.
			RequiredPorts
				.
				N =
				
				ProvidedPorts
				.M
				);
		}

		private void M()
		{
		}

		private extern void N();
	}

	[CheckTrivia(TriviaType.DocCommentsAndDirectives)]
	partial class Out13 : Component
	{
		private Out13 i;

		private Out13()
		{
			global::SafetySharp.CompilerServices.MetadataBuilders.GetBuilder(this).WithBinding((__BindingDelegate0__)(i.N), (__BindingDelegate0__)(M));
#line 44
		}

		private void M()
		{
		}

		private extern void N();
	}

	partial class Out13
	{
		[System.Runtime.CompilerServices.CompilerGeneratedAttribute]
		private delegate void __BindingDelegate0__();
	}
}