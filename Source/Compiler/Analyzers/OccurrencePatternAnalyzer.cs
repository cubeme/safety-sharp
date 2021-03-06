﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Compiler.Analyzers
{
	using System;
	using System.Linq;
	using JetBrains.Annotations;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Microsoft.CodeAnalysis.Diagnostics;
	using Modeling.Faults;
	using Roslyn;
	using Roslyn.Symbols;
	using Roslyn.Syntax;

	/// <summary>
	///     Ensures that a fault declaration is marked with exactly one <see cref="OccurrencePatternAttribute" />.
	/// </summary>
	[DiagnosticAnalyzer(LanguageNames.CSharp), UsedImplicitly]
	public sealed class OccurrencePatternAnalyzer : Analyzer
	{
		/// <summary>
		///     Indicates that the occurrence pattern is missing.
		/// </summary>
		private static readonly DiagnosticInfo _missingPattern = DiagnosticInfo.Error(
			DiagnosticIdentifier.MissingOccurrencePattern,
			"A fault must be marked with a default occurrence pattern.",
			String.Format(
				"Fault '{{0}}' does not declare a default occurrence pattern. Mark it with an instance of '{0}'. " +
				"You can change the default occurrence pattern dynamically during model initialization time.",
				typeof(OccurrencePatternAttribute).FullName));

		/// <summary>
		///     Indicates that multiple occurrence patterns are provided.
		/// </summary>
		private static readonly DiagnosticInfo _ambiguousPattern = DiagnosticInfo.Error(
			DiagnosticIdentifier.AmbiguousOccurrencePattern,
			"A fault cannot be marked with more than one default occurrence pattern.",
			"Fault '{0}' cannot be marked with more than one occurrence pattern.");

		/// <summary>
		///     Indicates that a non-fault class is marked with an occurrence pattern.
		/// </summary>
		private static readonly DiagnosticInfo _occurrencePatternHasNoEffect = DiagnosticInfo.Warning(
			DiagnosticIdentifier.OccurrencePatternHasNoEffect,
			"Marking a non-fault class with an occurrence pattern has no effect.",
			String.Format("Occurrence patterns have no effect on classes not derived from '{0}'.", typeof(Fault).FullName));

		/// <summary>
		///     Indicates that a non-<see cref="OccurrencePattern" />-derived class is passed to the constructor of the
		///     <see cref="OccurrencePatternAttribute" />.
		/// </summary>
		private static readonly DiagnosticInfo _nonOccurrencePatternType = DiagnosticInfo.Warning(
			DiagnosticIdentifier.NonOccurrencePatternType,
			String.Format("Occurrence patterns must be derived from '{0}'.", typeof(OccurrencePattern).FullName),
			String.Format("Expected a type derived from '{0}'.", typeof(OccurrencePattern).FullName));

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public OccurrencePatternAnalyzer()
			: base(_missingPattern, _ambiguousPattern, _occurrencePatternHasNoEffect, _nonOccurrencePatternType)
		{
		}

		/// <summary>
		///     Called once at session start to register actions in the analysis context.
		/// </summary>
		/// <param name="context" />
		public override void Initialize(AnalysisContext context)
		{
			context.RegisterSymbolAction(Analyze, SymbolKind.NamedType);
			context.RegisterSyntaxNodeAction(AnalyzeConstructorDeclaration, SyntaxKind.ConstructorDeclaration);
			context.RegisterSyntaxNodeAction(AnalyzeAttribute, SyntaxKind.Attribute);
		}

		/// <summary>
		///     Checks whether the constructor assigns an invalid type to <see cref="OccurrencePatternAttribute" />'s
		///     constructor argument.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void AnalyzeAttribute(SyntaxNodeAnalysisContext context)
		{
			var semanticModel = context.SemanticModel;
			var attributeArgument = (AttributeSyntax)context.Node;
			var constructorSymbol = semanticModel.GetSymbolInfo(attributeArgument).Symbol;

			if (!constructorSymbol.ContainingType.Equals(semanticModel.GetTypeSymbol<OccurrencePatternAttribute>()))
				return;

			var typeofExpression = (TypeOfExpressionSyntax)attributeArgument.ArgumentList.Arguments[0].Expression;
			var occurrencePatternTypeSymbol = typeofExpression.Type.GetReferencedSymbol<INamedTypeSymbol>(semanticModel);

			if (!occurrencePatternTypeSymbol.IsDerivedFrom(semanticModel.GetTypeSymbol<OccurrencePattern>()))
				_nonOccurrencePatternType.Emit(context, typeofExpression.Type, occurrencePatternTypeSymbol.ToDisplayString());;
		}

		/// <summary>
		///     Checks whether the constructor assigns an invalid type to <see cref="OccurrencePatternAttribute" />'s
		///     constructor argument.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void AnalyzeConstructorDeclaration(SyntaxNodeAnalysisContext context)
		{
			var semanticModel = context.SemanticModel;
			var constructorDeclaration = (ConstructorDeclarationSyntax)context.Node;
			var constructorSymbol = constructorDeclaration.GetMethodSymbol(semanticModel);

			if (!constructorSymbol.ContainingType.IsDerivedFrom(semanticModel.GetTypeSymbol<OccurrencePatternAttribute>()))
				return;

			var typeofExpression = (TypeOfExpressionSyntax)constructorDeclaration.Initializer.ArgumentList.Arguments[0].Expression;
			var occurrencePatternTypeSymbol = typeofExpression.Type.GetReferencedSymbol<INamedTypeSymbol>(semanticModel);

			if (!occurrencePatternTypeSymbol.IsDerivedFrom(semanticModel.GetTypeSymbol<OccurrencePattern>()))
				_nonOccurrencePatternType.Emit(context, typeofExpression.Type, occurrencePatternTypeSymbol.ToDisplayString());
		}

		/// <summary>
		///     Performs the analysis.
		/// </summary>
		/// <param name="context">The context in which the analysis should be performed.</param>
		private static void Analyze(SymbolAnalysisContext context)
		{
			var compilation = context.Compilation;
			var symbol = context.Symbol as ITypeSymbol;

			if (symbol == null)
				return;

			var isFault = symbol.IsDerivedFromFault(compilation);
			var attributeSymbol = compilation.GetOccurrencePatternAttributeSymbol();
			var count = symbol
				.GetAttributes()
				.Count(attribute => attribute.AttributeClass.Equals(attributeSymbol) || attribute.AttributeClass.IsDerivedFrom(attributeSymbol));

			if (count != 0 && !isFault)
				_occurrencePatternHasNoEffect.Emit(context, symbol);

			if (!isFault)
				return;

			if (count == 0)
				_missingPattern.Emit(context, symbol, symbol.ToDisplayString());
			else if (count > 1)
				_ambiguousPattern.Emit(context, symbol, symbol.ToDisplayString());
		}
	}
}