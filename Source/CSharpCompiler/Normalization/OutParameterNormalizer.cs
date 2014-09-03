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

namespace SafetySharp.CSharpCompiler.Normalization
{
	using System;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;
	using Roslyn.Syntax;

	/// <summary>
	///     Replaces all out parameters of a method declaration or method invocation with ref parameters. This normalization assumes
	///     that the variable is definitely assigned before the method invocation; otherwise, invalid C# code is generated.
	/// 
	///     For instance:
	///     <code>
	///  		public void MyMethod(out int a) { ... }
	///  		// becomes:
	///  		public void MyMethod(ref int a) { ... }
	///  		
	///  		MyMethod(out x);
	///  		// becomes:
	///  		MyMethod(ref x);
	/// 	</code>
	/// </summary>
	public class OutParameterNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public OutParameterNormalizer()
			: base(NormalizationScope.Components)
		{
		}

		/// <summary>
		///     Replaces the <paramref name="parameter" />'s out modifier with a ref modifier.
		/// </summary>
		public override SyntaxNode VisitParameter(ParameterSyntax parameter)
		{
			if (!parameter.Modifiers.Any(SyntaxKind.OutKeyword))
				return parameter;

			var outModifier = parameter.Modifiers.SingleOrDefault(token => token.CSharpKind() == SyntaxKind.OutKeyword);
			var refModifier = SyntaxFactory.Token(SyntaxKind.RefKeyword).WithTrivia(outModifier);
			return parameter.WithModifiers(parameter.Modifiers.Replace(outModifier, refModifier));
		}

		/// <summary>
		///     Replaces the <paramref name="argument" />'s out modifier with a ref modifier.
		/// </summary>
		public override SyntaxNode VisitArgument(ArgumentSyntax argument)
		{
			if (argument.RefOrOutKeyword.CSharpKind() != SyntaxKind.OutKeyword)
				return argument;

			var refModifier = SyntaxFactory.Token(SyntaxKind.RefKeyword).WithTrivia(argument.RefOrOutKeyword);
			return argument.WithRefOrOutKeyword(refModifier);
		}
	}
}