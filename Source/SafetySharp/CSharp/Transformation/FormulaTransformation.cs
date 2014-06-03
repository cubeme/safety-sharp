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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Globalization;
	using System.Linq;
	using Extensions;
	using Formulas;
	using Metamodel;
	using Metamodel.Expressions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Transforms all <see cref="UntransformedStateFormula" />s contained in a <see cref="LtlFormula" /> to the
	///     corresponding transformed <see cref="StateFormula" />s.
	/// </summary>
	internal class FormulaTransformation : FormulaRewriter
	{
		/// <summary>
		///     The prefix used for generated names to ensure their uniqueness.
		/// </summary>
		private const string GeneratedNamePrefix = "CD160172C5924ED387C2B31D7C4EA3DE";

		/// <summary>
		///     The code template that is used to parse the C# expressions of the state formulas.
		/// </summary>
		private const string CodeTemplate = @"
			class CD160172C5924ED387C2B31D7C4EA3DE
			{{
				bool M()
				{{
					{0}
					return {1};
				}}
			}}";

		/// <summary>
		///     The modeling compilation that defines the types referenced by the formula.
		/// </summary>
		private readonly ModelingCompilation _compilation;

		/// <summary>
		///     The component resolver that is used to resolve components to their configurations.
		/// </summary>
		private readonly ComponentResolver _componentResolver;

		/// <summary>
		///     The resolver that is used to resolve metamodel references.
		/// </summary>
		private readonly MetamodelResolver _metamodelResolver;

		/// <summary>
		///     The symbol map that can be used to look up metamodel element references for C# symbols.
		/// </summary>
		private readonly SymbolMap _symbolMap;

		/// <summary>
		///     Initializes a new instance of the <see cref="FormulaTransformation" /> type.
		/// </summary>
		/// <param name="compilation">The modeling compilation that defines the types referenced by the formula.</param>
		/// <param name="symbolMap">The symbol map that should be used to look up metamodel element references for C# symbols.</param>
		/// <param name="componentResolver">The component resolver that should be used to resolve components to their configurations.</param>
		/// <param name="metamodelResolver">The resolver that should be used to resolve metamodel references.</param>
		public FormulaTransformation(ModelingCompilation compilation, SymbolMap symbolMap,
									 ComponentResolver componentResolver, MetamodelResolver metamodelResolver)
		{
			Argument.NotNull(compilation, () => compilation);
			Argument.NotNull(symbolMap, () => symbolMap);
			Argument.NotNull(componentResolver, () => componentResolver);
			Argument.NotNull(metamodelResolver, () => metamodelResolver);

			_compilation = compilation;
			_symbolMap = symbolMap;
			_componentResolver = componentResolver;
			_metamodelResolver = metamodelResolver;

			FormulaResolver = FormulaResolver.Empty;
		}

		/// <summary>
		///     Gets or sets the <see cref="FormulaResolver" /> that is updated during the transformation.
		/// </summary>
		internal FormulaResolver FormulaResolver { get; private set; }

		/// <summary>
		///     Rewrites an element of type <see cref="UntransformedStateFormula" />.
		/// </summary>
		/// <param name="untransformedStateFormula">The <see cref="UntransformedStateFormula" /> instance that should be rewritten.</param>
		public override Formula VisitUntransformedStateFormula(UntransformedStateFormula untransformedStateFormula)
		{
			Argument.NotNull(untransformedStateFormula, () => untransformedStateFormula);

			var declarations = String.Join(String.Empty, GetDeclarations(untransformedStateFormula.Values));
			var formattedExpression = String.Format(untransformedStateFormula.Expression,
													GetExpressionFormatArguments(untransformedStateFormula.Values).ToArray());
			var code = String.Format(CodeTemplate, declarations, formattedExpression);

			var syntaxTree = SyntaxFactory.ParseSyntaxTree(code);
			var expression = syntaxTree.DescendantNodes<ReturnStatementSyntax>().Single().Expression;

			var compilation = _compilation.CSharpCompilation.AddSyntaxTrees(syntaxTree);
			var diagnostics = compilation
				.GetDiagnostics()
				.Where(diagnostic => diagnostic.Severity == DiagnosticSeverity.Error)
				.Select(diagnostic => diagnostic.GetMessage())
				.ToImmutableArray();

			if (diagnostics.Length != 0)
				throw new InvalidOperationException(String.Format("Malformed state formula '{0}':{1}{2}", expression,
																  Environment.NewLine, String.Join(Environment.NewLine, diagnostics)));

			var semanticModel = compilation.GetSemanticModel(syntaxTree);
			var expressionTransformation = new Transformation(semanticModel, _symbolMap)
			{
				ComponentResolver = _componentResolver,
				FormulaResolver = FormulaResolver,
				FormulaValues = untransformedStateFormula.Values,
				MetamodelResolver = _metamodelResolver
			};

			var transformedExpression = expressionTransformation.Transform(expression);
			FormulaResolver = expressionTransformation.FormulaResolver;

			return new StateFormula(transformedExpression, null);
		}

		/// <summary>
		///     Gets the required declarations for <paramref name="values" /> that are required to compile the C# expression.
		/// </summary>
		/// <param name="values">The values that are referenced by the C# expression.</param>
		private static IEnumerable<string> GetDeclarations(ImmutableArray<object> values)
		{
			var index = 0;
			foreach (var value in values)
			{
				if (value is Component)
					yield return String.Format("{0} {1}_{2} = null;", value.GetType().FullName, GeneratedNamePrefix, index);
				else if (value is IInternalAccess)
					yield return String.Format("{0} {1}_{2} = null;", ((IInternalAccess)value).Component.GetType().FullName, GeneratedNamePrefix, index);

				++index;
			}
		}

		/// <summary>
		///     Gets the arguments for <paramref name="values" /> that are required to format the C# expression.
		/// </summary>
		/// <param name="values">The values that are referenced by the C# expression.</param>
		private static IEnumerable<object> GetExpressionFormatArguments(ImmutableArray<object> values)
		{
			var index = 0;
			foreach (var value in values)
			{
				if (value is Component)
					yield return String.Format("{0}_{1}", GeneratedNamePrefix, index);
				else if (value is IInternalAccess)
					yield return String.Format("{0}_{1}.{2}", GeneratedNamePrefix, index, ((IInternalAccess)value).MemberName);
				else if (value is bool)
					yield return (bool)value ? "true" : "false";
				else if (value is int)
					yield return ((int)value).ToString(CultureInfo.InvariantCulture);
				else if (value is decimal)
					yield return ((decimal)value).ToString(CultureInfo.InvariantCulture) + "m";
				else
					throw new InvalidOperationException(String.Format("State formula references unsupported type '{0}'.", value.GetType().FullName));

				++index;
			}
		}

		/// <summary>
		///     Transforms a lowered C# syntax tree of an expression into a corresponding formula expression tree.
		/// </summary>
		private class Transformation : ExpressionTransformation
		{
			/// <summary>
			///     Initializes a new instance of the <see cref="Transformation" /> type.
			/// </summary>
			/// <param name="semanticModel">The semantic model that should be used to retrieve semantic information about the C# program.</param>
			/// <param name="symbolMap">The symbol map that should be used to look up metamodel element references for C# symbols.</param>
			internal Transformation(SemanticModel semanticModel, SymbolMap symbolMap)
				: base(semanticModel, symbolMap)
			{
			}

			/// <summary>
			///     Gets or sets the component resolver that is used to resolve components to their configurations.
			/// </summary>
			public ComponentResolver ComponentResolver { get; set; }

			/// <summary>
			///     Gets or sets the resolver that is used to resolve metamodel references.
			/// </summary>
			public MetamodelResolver MetamodelResolver { get; set; }

			/// <summary>
			///     Gets or sets the values provided to the formula.
			/// </summary>
			public ImmutableArray<object> FormulaValues { get; set; }

			/// <summary>
			///     Gets or sets the <see cref="FormulaResolver" /> that is updated during the transformation.
			/// </summary>
			public FormulaResolver FormulaResolver { get; set; }

			/// <summary>
			///     Transforms a <see cref="MemberAccessExpressionSyntax" /> to the corresponding component field access.
			/// </summary>
			/// <param name="node">The member access expression that should be transformed.</param>
			public override MetamodelElement VisitMemberAccessExpression(MemberAccessExpressionSyntax node)
			{
				Assert.That(SemanticModel.GetSymbolInfo(node.Name).Symbol as IFieldSymbol != null, "Expected a field member.");
				Assert.That(!(node.Expression is MemberAccessExpressionSyntax), "Nested member accesses are not supported.");

				var fieldAccess = (FieldAccessExpression)Visit(node.Name);
				var objectIndex = Int32.Parse(node.Expression.ToString().Split(new[] { "_" }, StringSplitOptions.RemoveEmptyEntries)[1]);
				Assert.InRange(objectIndex, FormulaValues);

				var component = FormulaValues[objectIndex] as Component;
				var internalAccess = FormulaValues[objectIndex] as IInternalAccess;
				if (internalAccess != null)
					component = internalAccess.Component;

				Assert.NotNull(component, "Unable to determine component instance.");

				var snapshot = component.GetSnapshot();
				var fieldDeclaration = MetamodelResolver.Resolve(fieldAccess.Field);
				var componentConfiguration = ComponentResolver.ResolveConfiguration(snapshot);
				var fieldConfiguration = componentConfiguration.Fields[fieldDeclaration];

				FormulaResolver = FormulaResolver.With(fieldAccess, fieldConfiguration);

				return fieldAccess;
			}
		}
	}
}