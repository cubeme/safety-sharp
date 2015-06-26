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

namespace Tests.Metadata.Components.ProvidedPorts
{
	using System;
	using System.Reflection;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal interface I1<T> : IComponent
	{
		[Provided]
		T P { get; }

		[Provided]
		T M();
	}

	internal interface I2 : IComponent
	{
		[Provided]
		int P { get; }

		[Provided]
		int M();
	}

	internal class X12 : TestComponent, I1<int>
	{
		public int M()
		{
			return 1;
		}

		public int P
		{
			get { return 0; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X12).GetMethod("M"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X12).GetMethod("get_P"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
		}
	}

	internal class X13 : TestComponent, I1<bool>
	{
		bool I1<bool>.M()
		{
			return false;
		}

		bool I1<bool>.P
		{
			get { return false; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(1);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X13).GetMethod("Tests.Metadata.Components.ProvidedPorts.I1<System.Boolean>.M",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<bool>).GetMethod("M") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("Tests_Metadata_Components_ProvidedPorts_I1__System_Boolean___M");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X13).GetMethod("Tests.Metadata.Components.ProvidedPorts.I1<System.Boolean>.get_P",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<bool>).GetMethod("get_P") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("Tests_Metadata_Components_ProvidedPorts_I1__System_Boolean___get_P");
		}
	}

	internal abstract class X14 : TestComponent, I1<bool>, I1<int>
	{
		bool I1<bool>.M()
		{
			return false;
		}

		bool I1<bool>.P
		{
			get { return true; }
		}

		public int M()
		{
			return 1;
		}

		public int P
		{
			get { return 1; }
		}
	}

	internal class X15 : X14
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(4);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X14).GetMethod("Tests.Metadata.Components.ProvidedPorts.I1<System.Boolean>.M",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<bool>).GetMethod("M") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("Tests_Metadata_Components_ProvidedPorts_I1__System_Boolean___M");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X14).GetMethod("Tests.Metadata.Components.ProvidedPorts.I1<System.Boolean>.get_P",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<bool>).GetMethod("get_P") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("Tests_Metadata_Components_ProvidedPorts_I1__System_Boolean___get_P");

			Metadata.ProvidedPorts[2].MethodInfo.ShouldBe(typeof(X14).GetMethod("M"));
			Metadata.ProvidedPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[2].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[2].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[2].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[2].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[2].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[2].Name.ShouldBe("M");

			Metadata.ProvidedPorts[3].MethodInfo.ShouldBe(typeof(X14).GetProperty("P").GetMethod);
			Metadata.ProvidedPorts[3].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[3].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[3].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[3].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[3].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[3].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[3].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[3].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetProperty("P").GetMethod });
			Metadata.ProvidedPorts[3].Name.ShouldBe("get_P");
		}
	}

	internal abstract class X16 : TestComponent, I1<int>
	{
		public abstract int M();
		public abstract int P { get; }
	}

	internal class X17 : X16
	{
		public override int P
		{
			get { return 1; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X17).GetMethod("P"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X17).GetMethod("M"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("M");
		}

		public override int M()
		{
			return 0;
		}
	}

	internal abstract class X18 : TestComponent, I1<int>
	{
		public virtual int P
		{
			get { return 1; }
		}

		public virtual int M()
		{
			return 0;
		}
	}

	internal class X19 : X18
	{
		public override int P
		{
			get { return 2; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(4);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X18).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(true);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[2]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X18).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(true);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[3]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");

			Metadata.ProvidedPorts[2].MethodInfo.ShouldBe(typeof(X19).GetMethod("get_P"));
			Metadata.ProvidedPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[2].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[2].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[2].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[2].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[2]);
			Metadata.ProvidedPorts[2].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[2].Name.ShouldBe("get_P1");

			Metadata.ProvidedPorts[3].MethodInfo.ShouldBe(typeof(X19).GetMethod("M"));
			Metadata.ProvidedPorts[3].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[3].BaseMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[3].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[3].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[3].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[3].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[3].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[3]);
			Metadata.ProvidedPorts[3].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[3].Name.ShouldBe("M1");
		}

		public override int M()
		{
			return 1;
		}
	}

	internal abstract class X20 : TestComponent
	{
		public int P
		{
			get { return 1; }
		}

		public int M()
		{
			return 0;
		}
	}

	internal class X21 : X20, I1<int>
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X20).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X20).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");
		}
	}

	internal abstract class X22 : TestComponent, I1<int>
	{
		public int P
		{
			get { return 1; }
		}

		public int M()
		{
			return 0;
		}
	}

	internal class X23 : X22, I1<int>
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X22).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X22).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");
		}
	}

	internal abstract class X24 : TestComponent
	{
		public virtual int P
		{
			get { return 0; }
		}

		public virtual int M()
		{
			return 0;
		}
	}

	internal class X25 : X24, I1<int>
	{
		public override int P
		{
			get { return 1; }
		}

		public override int M()
		{
			return 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(4);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X24).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(true);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[2]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X24).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(true);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[3]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");

			Metadata.ProvidedPorts[2].MethodInfo.ShouldBe(typeof(X25).GetMethod("get_P"));
			Metadata.ProvidedPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[2].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[2].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[2].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[2].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[2]);
			Metadata.ProvidedPorts[2].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[2].Name.ShouldBe("get_P1");

			Metadata.ProvidedPorts[3].MethodInfo.ShouldBe(typeof(X25).GetMethod("M"));
			Metadata.ProvidedPorts[3].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[3].BaseMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[3].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[3].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[3].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[3].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[3].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[3]);
			Metadata.ProvidedPorts[3].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[3].Name.ShouldBe("M1");
		}
	}

	internal abstract class X26 : TestComponent
	{
		public abstract int P { get; }
		public abstract int M();
	}

	internal class X27 : X26, I1<int>
	{
		public override int P
		{
			get { return 1; }
		}

		public override int M()
		{
			return 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X27).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X27).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");
		}
	}

	internal abstract class X28 : TestComponent, I1<int>
	{
		public abstract int P { get; }
		public abstract int M();
	}

	internal class X29 : X28
	{
		public override int P
		{
			get { return 1; }
		}

		public override int M()
		{
			return 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X29).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X29).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");
		}
	}

	internal abstract class X30 : TestComponent, I1<int>
	{
		public abstract int P { get; }
		public abstract int M();
	}

	internal class X31 : X30, I2
	{
		public override int P
		{
			get { return 1; }
		}

		public override int M()
		{
			return 1;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X31).GetMethod("get_P"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("get_P"), typeof(I2).GetMethod("get_P") });
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X31).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I1<int>).GetMethod("M"), typeof(I2).GetMethod("M") });
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");
		}
	}

	internal interface I3 : IComponent
	{
		[Provided]
		int P { set; }

		[Provided]
		bool F(bool b);

		[Provided]
		int G(ref int a);

		[Provided]
		int H(int a);
	}

	internal abstract class X32 : TestComponent, I3
	{
		bool I3.F(bool s)
		{
			return !s;
		}

		int I3.G(ref int t)
		{
			return t - 3;
		}

		public virtual int H(int q)
		{
			return q + q - 3;
		}

		public virtual int P
		{
			set { }
		}
	}

	internal class X33 : X32, I3
	{
		int I3.H(int r)
		{
			return base.H(r) - 5;
		}

		int I3.P
		{
			set { }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(6);

			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBe(new[] { typeof(I3).GetMethod("F") });
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBe(new[] { typeof(I3).GetMethod("G") });
			Metadata.ProvidedPorts[2].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[3].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[4].ImplementedMethods.ShouldBe(new[] { typeof(I3).GetMethod("H") });
			Metadata.ProvidedPorts[5].ImplementedMethods.ShouldBe(new[] { typeof(I3).GetMethod("set_P") });
		}
	}
}