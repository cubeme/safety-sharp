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

namespace SafetySharp.CSharp.Runtime
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Extensions;
	using Metamodel;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides metadata about Safety Sharp types in a Safety Sharp modeling assembly.
	/// </summary>
	public abstract class ModelingAssembly
	{
		/// <summary>
		///     Gets the C# source code for the syntax trees containing the Safety Sharp models of the assembly.
		/// </summary>
		protected abstract IEnumerable<string> SyntaxTrees { get; }

		/// <summary>
		///     Gets the compilation for the Safety Sharp types in the modeling assembly and all of its
		///     dependent modeling assemblies.
		/// </summary>
		public Compilation Compilation
		{
			get
			{
				// TODO: Include dependent modeling assemblies into the compilation
				return CSharpCompilation
					.Create("ModelingAssembly")
					.AddReferences(new MetadataFileReference(typeof(object).Assembly.Location))
					.AddReferences(new MetadataFileReference(typeof(MetamodelElement).Assembly.Location))
					.AddSyntaxTrees(SyntaxTrees.Select(syntaxTree => SyntaxFactory.ParseSyntaxTree(syntaxTree)));
			}
		}

		/// <summary>
		///     Generates the <see cref="ModelingAssembly" /> implementing class for the given compilation.
		/// </summary>
		/// <param name="compilation">The compilation the <see cref="ModelingAssembly" /> implementing class should be generated for.</param>
		public static Compilation GenerateImplementingClass(Compilation compilation)
		{
			Argument.NotNull(compilation, () => compilation);
			var writer = new CodeWriter();

			writer.AppendLine("using System;");
			writer.AppendLine("using System.Collections.Generic;");
			writer.AppendLine("using {0};", typeof(Component).Namespace);

			var prefix = Guid.NewGuid().ToString().GetHashCode();
			writer.AppendLine("public class {0}{1:X} : {2}", typeof(ModelingAssembly).Name, prefix, typeof(ModelingAssembly).FullName);
			writer.AppendBlockStatement(() =>
			{
				writer.AppendLine("protected override IEnumerable<string> SyntaxTrees");
				writer.AppendBlockStatement(() =>
				{
					writer.AppendLine("get");
					writer.AppendBlockStatement(() =>
					{
						writer.AppendLine("return new [] {{");
						writer.AppendSeparated(
							values: compilation.SyntaxTrees.Where(syntaxTree => compilation.GetSemanticModel(syntaxTree).GetDeclaredComponents().Any()),
							separator: ",",
							content: component => writer.Append("@\"{0}\"", component));
						writer.AppendLine("}};");
					});
				});
			});

			var csharpCode = writer.ToString();
			var parsedCode = SyntaxFactory.ParseSyntaxTree(csharpCode);
			return compilation.AddSyntaxTrees(parsedCode);
		}
	}
}