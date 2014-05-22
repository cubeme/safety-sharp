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
        // https://bitbucket.org/Axel777/safetysharp/src/2e0a77c3a9088567a878698a50c0f563eb58eb25/Source/Tests/Tests.cs?at=master


        [Test]
        public void Test()
        {
            var fieldDeclReference = new MM.MetamodelReference<MMDeclarations.FieldDeclaration>();
            var fieldDecl = new MMDeclarations.FieldDeclaration(new MM.Identifier("_value"), MMTypes.TypeSymbol.Boolean);

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

            var trueAndFalseValues = ImmutableArray<MMConfigurations.Value>.Empty
                .Add(new MMConfigurations.Value(true))
                .Add(new MMConfigurations.Value(false));
            var trueAndFalsePossible =  new MMConfigurations.ValueArray(trueAndFalseValues);
            // a component has a list of fields which themselves may have more possible start values
            var initialValues = ImmutableArray<MMConfigurations.ValueArray>.Empty
                    .Add(trueAndFalsePossible);

            var subcomponentInstances = ImmutableArray<MMConfigurations.ComponentConfiguration>.Empty;

            var componentDeclReference = new MM.MetamodelReference<MMDeclarations.ComponentDeclaration>();
            var mmsimpleComponentInstance = new MMConfigurations.ComponentConfiguration(
                new MM.Identifier("BooleanComponentConfiguration"),
                componentDeclReference,
                initialValues,
                subcomponentInstances);

            var partition = new MMConfigurations.Partition(mmsimpleComponentInstance);

            var completeMetamodel = new MM.MetamodelConfiguration(ImmutableArray<MMConfigurations.Partition>.Empty.Add(partition));

            var mmAccessTypeToConcreteTypeDictionary = MM.MetamodelResolver.Empty;
            mmAccessTypeToConcreteTypeDictionary = mmAccessTypeToConcreteTypeDictionary.With(fieldDeclReference, fieldDecl);
            mmAccessTypeToConcreteTypeDictionary = mmAccessTypeToConcreteTypeDictionary.With(componentDeclReference, mmsimpleComponentDecl);


            var metamodelToPromela = new MetamodelToPromela(completeMetamodel, mmAccessTypeToConcreteTypeDictionary);

            var convertedMetamodel = metamodelToPromela.ConvertMetaModelConfiguration();

            var filename = "Modelchecking\\Promela\\test2.pml";

            var modelWriter = new PromelaModelWriter();
            modelWriter.Visit(convertedMetamodel);

            modelWriter.CodeWriter.WriteToFile(filename);

            Spin.ExecuteSpin("-a " + filename).Should().Be(Spin.SpinResult.Success);
        }
    }
}