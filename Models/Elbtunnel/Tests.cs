namespace Elbtunnel
{
	using System;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		[Test]
		public void FirstTest()
		{
			Console.WriteLine("Test");
			var spin = new SpinModelChecker(new BooleanComponent());
		}

		class X(private int i)
	{
		
	}

		static void Main(string[] args)
		{
			var x = new X(1);
			var spin = new SpinModelChecker(new BooleanComponent());
		}
	}
}