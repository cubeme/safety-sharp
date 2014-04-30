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

namespace Tests.Metamodel
{
	using System;
	using CSharp.Transformation;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Metamodel;

	[TestFixture]
	internal class ReferenceTests : TransformationVisitorTests
	{
		[Test]
		public void Equality()
		{
			var reference1 = new Reference<MetamodelElement>(1);
			var reference2 = new Reference<MetamodelElement>(2);
			var reference3 = new Reference<MetamodelElement>(2);

			reference1.Equals(null).Should().BeFalse();
			reference1.Equals(reference1).Should().BeTrue();
			reference1.Equals(reference2).Should().BeFalse();
			reference2.Equals(reference3).Should().BeTrue();
			reference1.Equals((object)reference1).Should().BeTrue();
			reference1.Equals((object)reference2).Should().BeFalse();
			reference2.Equals((object)reference3).Should().BeTrue();
			(reference1 == reference2).Should().BeFalse();
			(reference3 == reference2).Should().BeTrue();
		}

		[Test]
		public void Inequality()
		{
			var reference1 = new Reference<MetamodelElement>(1);
			var reference2 = new Reference<MetamodelElement>(2);
			var reference3 = new Reference<MetamodelElement>(2);

			(reference1 != reference2).Should().BeTrue();
			(reference3 != reference2).Should().BeFalse();
		}
	}
}