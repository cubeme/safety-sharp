namespace Elbtunnel
{
	using System;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		private class Q
		{
			private int i = 47;

			public Q()
			{
				Console.WriteLine(i);
			}

			public Q(int x)
				: this()
			{
				Console.WriteLine(i);
			}
		}

		private class Configuration : ModelConfiguration
		{
			public Configuration(bool nondeterministicInitialValue)
			{
				AddPartitions(new BooleanComponent(nondeterministicInitialValue), new BooleanComponent(false));
			}
		}

		private static void Main(string[] args)
		{
			var spin = new SpinModelChecker(new Configuration(true));
		}

		[Test]
		public void FirstTest()
		{
			Console.WriteLine("Test");
			var spin = new SpinModelChecker(new Configuration(true));
		}
	}
}