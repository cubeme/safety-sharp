namespace Elbtunnel
{
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		[Test]
		public void FirstTest()
		{
			var spin = new SpinModelChecker(new BooleanComponent());
		}
	}
}