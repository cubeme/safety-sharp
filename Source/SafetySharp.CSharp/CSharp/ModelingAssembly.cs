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

namespace SafetySharp.CSharp
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using System.Reflection;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents a Safety Sharp modeling assembly.
	/// </summary>
	internal class ModelingAssembly
	{
		/// <summary>
		///     The C# assembly representing the modeling assembly.
		/// </summary>
		private readonly Assembly _assembly;

		/// <summary>
		///     Initializes a new instance of the <see cref="ModelingAssembly" /> type.
		/// </summary>
		/// <param name="modelingAssembly">The C# assembly representing the modeling assembly.</param>
		internal ModelingAssembly(Assembly modelingAssembly)
		{
			Requires.NotNull(modelingAssembly, () => modelingAssembly);
			_assembly = modelingAssembly;

			var assemblyMetadata = modelingAssembly.GetCustomAttribute<ModelingAssemblyAttribute>();
			Requires.ArgumentSatisfies(assemblyMetadata != null, () => modelingAssembly, "Expected a Safety Sharp modeling assembly.");

			CompilerVersion = assemblyMetadata.CompilerVersion;
			if (CompilerVersion != Compiler.Version)
				Log.Die("Modeling assembly '{0}' was compiled with a different version of the Safety Sharp compiler.", _assembly.FullName);
		}

		/// <summary>
		///     Gets the version string of the Safety Sharp compiler that was used to compile the modeling assembly.
		/// </summary>
		internal string CompilerVersion { get; private set; }

		/// <summary>
		///     Gets the C# <see cref="Compilation" /> representing the source code of the modeling assembly and of all of its dependent
		///     modeling assemblies.
		/// </summary>
		internal ModelingCompilation Compilation
		{
			get
			{
				var compilation = CSharpCompilation.Create("ModelingAssemblyMetadata",
														   options: new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));

				foreach (var assembly in _assembly.GetReferencedAssemblies().Select(Assembly.Load))
					compilation = compilation.AddReferences(new MetadataFileReference(assembly.Location));

				return new ModelingCompilation(AddCompilationUnits(compilation));
			}
		}

		/// <summary>
		///     Gets the modeling assemblies this modeling assembly depends on.
		/// </summary>
		internal IEnumerable<ModelingAssembly> DependentAssemblies
		{
			get
			{
				return _assembly
					.GetCustomAttributes<ModelingAssemblyReferenceAttribute>()
					.Select(assembly => new ModelingAssembly(Assembly.Load(assembly.AssemblyName)));
			}
		}

		/// <summary>
		///     Gets the C# <see cref="SyntaxTree" />s of all compilation units of the modeling assembly.
		/// </summary>
		internal IEnumerable<SyntaxTree> CompilationUnits
		{
			get
			{
				return _assembly
					.GetCustomAttributes<ModelingCompilationUnitAttribute>()
					.Select(compilationUnit => compilationUnit.SyntaxTree);
			}
		}

		/// <summary>
		///     Adds the modeling assembly's compilation units and all compilation units of the assembly's dependent assemblies to the
		///     <paramref name="compilation" />.
		/// </summary>
		/// <param name="compilation">The compilation the compilation units should be added to.</param>
		private Compilation AddCompilationUnits(Compilation compilation)
		{
			foreach (var dependentAssembly in DependentAssemblies)
				compilation = dependentAssembly.AddCompilationUnits(compilation);

			return compilation.AddSyntaxTrees(CompilationUnits);
		}
	}
}