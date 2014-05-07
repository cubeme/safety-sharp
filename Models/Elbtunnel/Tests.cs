namespace Elbtunnel
{
	using System;
	using System.Reflection;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		[Test]
		public void FirstTest()
		{
			Console.WriteLine("Test");
			//var spin = new SpinModelChecker(new BooleanComponent(1));
		}

		static void Main(string[] args)
		{
			new LightBarrier().Do();
			//var spin = new SpinModelChecker(new BooleanComponent(2));
		}
	}
}