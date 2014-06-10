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

namespace Tests.Modelchecking.Promela
{
	using System;
	using System.Collections.Immutable;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Formulas;
	using SafetySharp.Modelchecking.Promela;
	using MM = SafetySharp.Metamodel;
	using MMExpressions = SafetySharp.Metamodel.Expressions;
	using MMStatements = SafetySharp.Metamodel.Statements;
	using MMTypes = SafetySharp.Metamodel.Types;
	using MMDeclarations = SafetySharp.Metamodel.Declarations;
	using MMConfigurations = SafetySharp.Metamodel.Configurations;
	using PrExpressions = SafetySharp.Modelchecking.Promela.Expressions;
	using PrStatements = SafetySharp.Modelchecking.Promela.Statements;

	[TestFixture]
	public class MmToPromelaTestsSimple
	{
        /*
		[Test]
		public void Test()
		{
		    var mmFieldAccessExpressionToFieldConfiguration = FormulaResolver.Empty;

            var fieldDecl = new MMDeclarations.FieldDeclaration(new MM.Identifier("_value"), MMTypes.TypeSymbol.Boolean);
			var fieldDeclReference = new MM.MetamodelReference<MMDeclarations.FieldDeclaration>();
            var fieldAccessExpr = new MMExpressions.FieldAccessExpression(fieldDeclReference);


            var assignment1 = new MMStatements.AssignmentStatement(fieldAccessExpr, MMExpressions.BooleanLiteral.True);
			var assignment2 = new MMStatements.AssignmentStatement(fieldAccessExpr, MMExpressions.BooleanLiteral.False);

			var clause1 = new MMStatements.GuardedCommandClause(MMExpressions.BooleanLiteral.True, assignment1);
			var clause2 = new MMStatements.GuardedCommandClause(MMExpressions.BooleanLiteral.True, assignment2);

			var updateBody = new MMStatements.GuardedCommandStatement(ImmutableArray.Create(clause1, clause2));
			var updateMethod = MMDeclarations.MethodDeclaration.UpdateMethod.WithBody(updateBody.AsBlockStatement());

			var mmsimpleComponentDecl = new MMDeclarations.ComponentDeclaration(
				new MM.Identifier("BooleanComponentDeclaration"),
				updateMethod,
				ImmutableArray<MMDeclarations.MethodDeclaration>.Empty,
				ImmutableArray.Create(fieldDecl),
				ImmutableArray<MMDeclarations.SubComponentDeclaration>.Empty);

			var trueAndFalseValues = ImmutableArray.Create<object>(true, false);

			var fieldConfiguration = new MMConfigurations.FieldConfiguration(trueAndFalseValues);
			// a component has a list of fields which themselves may have more possible start values
			var initialValues = ImmutableDictionary<MMDeclarations.FieldDeclaration, MMConfigurations.FieldConfiguration>.Empty;
            initialValues = initialValues.Add(fieldDecl, fieldConfiguration);

            // connect a expression to the componentconfiguration it belongs to
		    mmFieldAccessExpressionToFieldConfiguration = mmFieldAccessExpressionToFieldConfiguration.With(fieldAccessExpr, fieldConfiguration);

            var subcomponentInstances = ImmutableArray<MMConfigurations.ComponentConfiguration>.Empty;

			var mmsimpleComponentInstance = new MMConfigurations.ComponentConfiguration(
				new MM.Identifier("BooleanComponentConfiguration"),
				mmsimpleComponentDecl,
				initialValues,
				subcomponentInstances);

            var partition = new MMConfigurations.Partition(mmsimpleComponentInstance);

			var completeMetamodel = new MM.MetamodelConfiguration(ImmutableArray<MMConfigurations.Partition>.Empty.Add(partition));

			var metamodelToPromela = new MetamodelToPromela(completeMetamodel, mmFieldAccessExpressionToFieldConfiguration);

			var modelWriter = new PromelaModelWriter();

			var filename = "Modelchecking\\Promela\\test2a.pml";
			var convertedMetamodel = metamodelToPromela.ConvertMetaModelConfiguration();
			modelWriter.Visit(convertedMetamodel);
			modelWriter.CodeWriter.WriteToFile(filename);
			Spin.ExecuteSpin("-a " + filename).Should().Be(Spin.SpinResult.Success);

			var formulaExpression1 = new MMExpressions.BinaryExpression(fieldAccessExpr, MMExpressions.BinaryOperator.Equals,
																		MMExpressions.BooleanLiteral.True);
			var formulaExpression2 = new MMExpressions.BinaryExpression(fieldAccessExpr, MMExpressions.BinaryOperator.Equals,
																		MMExpressions.BooleanLiteral.False);
			var formulaExpression1Or2 = new MMExpressions.BinaryExpression(formulaExpression1, MMExpressions.BinaryOperator.LogicalOr,
																		   formulaExpression2);
			var partitialFormula1 = new StateFormula(formulaExpression1Or2);
			var partitialFormula2 = new StateFormula(formulaExpression1);
			var formulaSatisfiedByModel = new UnaryFormula(partitialFormula1, UnaryTemporalOperator.Globally, PathQuantifier.None);
			var formulaNotSatisfiedByModel = new UnaryFormula(partitialFormula2, UnaryTemporalOperator.Globally, PathQuantifier.None);

			var convertedFormulaSatisfiedByModel = formulaSatisfiedByModel.Accept(metamodelToPromela.GetFormulaVisitor());
			var convertedFormulaNotSatisfiedByModel = formulaNotSatisfiedByModel.Accept(metamodelToPromela.GetFormulaVisitor());

			var convertedLtlFormulaModule = new LtlFormulaModule(null, convertedFormulaNotSatisfiedByModel);

			modelWriter.CodeWriter.NewLine();
			modelWriter.CodeWriter.NewLine();
			filename = "Modelchecking\\Promela\\test2b.pml";
			modelWriter.Visit(convertedLtlFormulaModule);
			modelWriter.CodeWriter.WriteToFile(filename);
			Spin.ExecuteSpin("-a " + filename).Should().Be(Spin.SpinResult.Success);
		}*/
	}
}