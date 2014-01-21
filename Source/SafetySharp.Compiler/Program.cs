namespace SafetySharp.Compiler
{
	using System;

	public class Program
	{
		private static void Main(string[] args)
		{
			Console.WriteLine();
			Console.WriteLine("============================================");
			Console.WriteLine("Running SafetySharp Compiler (ssc)...");
			Console.WriteLine();

			Console.WriteLine("Target assembly is located at: {0}", args[0]);
			Console.WriteLine("Target project is located at: {0}", args[1]);
			Console.WriteLine("============================================");
			Console.WriteLine();
		}
	}
}