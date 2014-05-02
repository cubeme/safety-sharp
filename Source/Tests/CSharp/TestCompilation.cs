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

namespace Tests.CSharp
{
	using System;
	using System.Linq;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.Metamodel;

	/// <summary>
	///     Represents a compiled C# compilation unit with a single syntax tree.
	/// </summary>
	internal class TestCompilation
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="csharpCode">The C# code that should be compiled.</param>
		public TestCompilation(string csharpCode)
		{
			var compilationUnit = SyntaxFactory.ParseCompilationUnit(csharpCode);
			SyntaxTree = compilationUnit.SyntaxTree;

			Compilation = CSharpCompilation
				.Create("Test")
				.AddReferences(new MetadataFileReference(typeof(object).Assembly.Location))
				.AddReferences(new MetadataFileReference(typeof(MetamodelElement).Assembly.Location))
				.AddSyntaxTrees(SyntaxTree);

			SemanticModel = Compilation.GetSemanticModel(SyntaxTree);
			SyntaxRoot = SyntaxTree.GetRoot();
		}

		/// <summary>
		///     Gets the C# compilation.
		/// </summary>
		public CSharpCompilation Compilation { get; private set; }

		/// <summary>
		///     Gets the syntax tree of the compilation.
		/// </summary>
		public SyntaxTree SyntaxTree { get; private set; }

		/// <summary>
		///     Gets the root syntax node of the syntax tree.
		/// </summary>
		public SyntaxNode SyntaxRoot { get; private set; }

		/// <summary>
		///     Gets the semantic model for the compilation's syntax tree.
		/// </summary>
		public SemanticModel SemanticModel { get; private set; }

		/// <summary>
		///     Finds the <see cref="ClassDeclarationSyntax" /> for the class named <paramref name="className" /> in the compilation.
		///     Throws an exception if more than one class with the given name was found.
		/// </summary>
		/// <param name="className">
		///     The name of the class that should be found in the format 'Namespace1.Namespace2.ClassName+NestedClass'.
		/// </param>
		internal ClassDeclarationSyntax FindClassDeclaration(string className)
		{
			var classes = SyntaxRoot
				.DescendantNodesAndSelf()
				.OfType<ClassDeclarationSyntax>()
				.Select(classDeclaration => new
				{
					ClassDeclaration = classDeclaration,
					FullName = classDeclaration.GetFullName(SemanticModel)
				})
				.Where(classDeclaration => classDeclaration.FullName == className)
				.ToArray();

			if (classes.Length == 0)
				throw new InvalidOperationException(String.Format("Found no classes with name '{0}'.", className));

			if (classes.Length > 1)
				throw new InvalidOperationException(String.Format("Found more than one class with name '{0}'.", className));

			return classes[0].ClassDeclaration;
		}

		/// <summary>
		///     Finds the <see cref="MethodDeclarationSyntax" /> for the method named <paramref name="methodName" /> in the class named
		///     <paramref name="className" /> within the compilation. Throws an exception if more than one class or method with the
		///     given name was found.
		/// </summary>
		/// <param name="className">
		///     The name of the class that contains the method that should be found in the format
		///     'Namespace1.Namespace2.ClassName+NestedClass'.
		/// </param>
		/// <param name="methodName">The name of the method that should be found.</param>
		internal MethodDeclarationSyntax FindMethodDeclaration(string className, string methodName)
		{
			var methods = FindClassDeclaration(className)
				.DescendantNodesAndSelf()
				.OfType<MethodDeclarationSyntax>()
				.Where(methodDeclaration => methodDeclaration.Identifier.ValueText == methodName)
				.ToArray();

			if (methods.Length == 0)
				throw new InvalidOperationException(String.Format("Found no methods with name '{0}' in '{1}'.", methodName, className));

			if (methods.Length > 1)
				throw new InvalidOperationException(String.Format("Found more than one method with name '{0}' in '{1}'.", methodName, className));

			return methods[0];
		}

		/// <summary>
		///     Finds the <see cref="VariableDeclaratorSyntax" /> for the field named <paramref name="fieldName" /> in the class named
		///     <paramref name="className" /> within the compilation. Throws an exception if more than one class or field with the
		///     given name was found.
		/// </summary>
		/// <param name="className">
		///     The name of the class that contains the field that should be found in the format
		///     'Namespace1.Namespace2.ClassName+NestedClass'.
		/// </param>
		/// <param name="fieldName">The name of the field that should be found.</param>
		internal VariableDeclaratorSyntax FindFieldDeclaration(string className, string fieldName)
		{
			var fields = FindClassDeclaration(className)
				.DescendantNodesAndSelf()
				.OfType<FieldDeclarationSyntax>()
				.SelectMany(fieldDeclaration => fieldDeclaration.Declaration.Variables)
				.Where(variableDeclaration => variableDeclaration.Identifier.ValueText == fieldName)
				.ToArray();

			if (fields.Length == 0)
				throw new InvalidOperationException(String.Format("Found no fields with name '{0}' in '{1}'.", fieldName, className));

			if (fields.Length > 1)
				throw new InvalidOperationException(String.Format("Found more than one field with name '{0}' in '{1}'.", fieldName, className));

			return fields[0];
		}

		/// <summary>
		///     Gets the <see cref="ITypeSymbol" /> representing the class with name <paramref name="className" />.
		/// </summary>
		/// <param name="className">
		///     The name of the class the symbol should be returned for in the format 'Namespace1.Namespace2.ClassName+NestedClass'.
		/// </param>
		internal ITypeSymbol FindClassSymbol(string className)
		{
			return SemanticModel.GetDeclaredSymbol(FindClassDeclaration(className));
		}

		/// <summary>
		///     Gets the <see cref="IMethodSymbol" /> representing the method with name <paramref name="methodName" /> in the class with
		///     name <paramref name="className" />.
		/// </summary>
		/// <param name="className">
		///     The name of the class that contains the method in the format 'Namespace1.Namespace2.ClassName+NestedClass'.
		/// </param>
		/// <param name="methodName">The name of the method that should be found.</param>
		internal IMethodSymbol FindMethodSymbol(string className, string methodName)
		{
			return SemanticModel.GetDeclaredSymbol(FindMethodDeclaration(className, methodName));
		}

		/// <summary>
		///     Gets the <see cref="IFieldSymbol" /> representing the field with name <paramref name="fieldName" /> in the class with
		///     name <paramref name="className" />.
		/// </summary>
		/// <param name="className">
		///     The name of the class that contains the field in the format 'Namespace1.Namespace2.ClassName+NestedClass'.
		/// </param>
		/// <param name="fieldName">The name of the field that should be found.</param>
		internal IFieldSymbol FindFieldSymbol(string className, string fieldName)
		{
			return (IFieldSymbol)SemanticModel.GetDeclaredSymbol(FindFieldDeclaration(className, fieldName));
		}
	}
}