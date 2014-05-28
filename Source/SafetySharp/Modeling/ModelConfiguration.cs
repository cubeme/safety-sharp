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

namespace SafetySharp.Modeling
{
	using System;
	using System.Linq.Expressions;

	public abstract partial class ModelConfiguration
	{
		/// <summary>
		///     Adds each component in <paramref name="components" /> as the root component of a partition to the model configuration.
		/// </summary>
		/// <param name="components">The components that should be added as root components of partitions.</param>
		protected void AddPartitions(params Component[] components)
		{
			AddPartitionsInternal(components);
		}

		partial void AddPartitionsInternal(Component[] components);

		public Formula LTL(string s)
		{
			return null;
		}
	}

	public class Formula
	{
		public static implicit operator Formula(bool value)
		{
			return null;
		}

		public Formula Implies(Formula f)
		{
			return f;
		}

		public Formula Implies(bool f)
		{
			return null;
		}

		public Formula AllowAccessTo(Component c, Func<dynamic, dynamic> f)
		{
			return this;
		}

		public Formula Ltl(string f)
		{
			return this;
		}
	}

	public static class Ltl
	{
		public static Formula Globally(Formula f)
		{
			return null;
		}

		public static Formula Globally(Expression<Func<Formula>> f)
		{
			return null;
		}

		public static Formula Globally(Expression<Func<bool>> f)
		{
			return null;
		}

		public static Formula Globally(bool f)
		{
			return null;
		}

		public static Formula StateFormula(bool f)
		{
			return null;
		}

		public static Formula Finally(Formula f)
		{
			return null;
		}

		public static dynamic AccessInternalsOf(Component c)
		{
			return c;
		}

		public static T AccessInternal<T>(this Component c, Func<dynamic, dynamic> val)
		{
			object o = val(c);
			return (T)o;
		}

		public static InternalAccess<T> AccessInternal<T>(this Component c, string val)
		{
			return default(InternalAccess<T>);
		}

		public static dynamic AllowAccessToInternals(this Component c)
		{
			return default(InternalAccess<bool>);
		}
	}

	public class InternalAccess<T>
	{
		public static implicit operator bool(InternalAccess<T> access)
		{
			return false;
		}
	}
}