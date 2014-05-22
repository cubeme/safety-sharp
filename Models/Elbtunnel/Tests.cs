namespace Elbtunnel
{
	using System;
	using NUnit.Framework;

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

		private static void Main(string[] args)
		{
			new Q(4);
			new LightBarrier().Do();
			//var spin = new SpinModelChecker(new BooleanComponent(2));
		}

		[Test]
		public void FirstTest()
		{
			Console.WriteLine("Test");
			//var spin = new SpinModelChecker(new BooleanComponent(1));
		}
	}
}