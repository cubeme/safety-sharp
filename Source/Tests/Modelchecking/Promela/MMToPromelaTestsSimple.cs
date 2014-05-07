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
    using MMInstances = SafetySharp.Metamodel.Instances;
    using PrExpressions = SafetySharp.Modelchecking.Promela.Expressions;
    using PrStatements = SafetySharp.Modelchecking.Promela.Statements;

    [TestFixture]
    public class MMToPromelaTestsSimple
    {
        // https://bitbucket.org/Axel777/safetysharp/src/2e0a77c3a9088567a878698a50c0f563eb58eb25/Source/Tests/Tests.cs?at=master

        [Test]
        public void Test()
        {
            var fieldSymbol = new Object();

            var fieldReference = new MM.MetamodelReference<MMDeclarations.FieldDeclaration>(fieldSymbol);
            var field = new MMDeclarations.FieldDeclaration(new MM.Identifier("_value"), MMTypes.TypeSymbol.Boolean);

            var fieldAccessExpr = new MMExpressions.FieldAccessExpression(fieldReference);

            var assignment1 = new MMStatements.AssignmentStatement(fieldAccessExpr, MMExpressions.BooleanLiteral.True);
            var assignment2 = new MMStatements.AssignmentStatement(fieldAccessExpr, MMExpressions.BooleanLiteral.False);

            var clause1 = new MMStatements.GuardedCommandClause(MMExpressions.BooleanLiteral.True, assignment1);
            var clause2 = new MMStatements.GuardedCommandClause(MMExpressions.BooleanLiteral.True, assignment2);

            var updateBody = new MMStatements.GuardedCommandStatement(ImmutableArray.Create(clause1, clause2));
            var updateMethod = MMDeclarations.MethodDeclaration.UpdateMethod.WithBody(updateBody.AsBlockStatement());

            var mmsimple = new MMDeclarations.ComponentDeclaration(new MM.Identifier("BooleanComponent"),
                                                    updateMethod,
                                                    ImmutableArray<MMDeclarations.MethodDeclaration>.Empty,
                                                    ImmutableArray.Create(field));

            var metamodelToPromela = new MetamodelToPromela();

            var nameOfField = metamodelToPromela.GetUniqueName(field);

            var promelaFieldAccess = fieldAccessExpr.Accept(metamodelToPromela.ExpressionVisitor);
            promelaFieldAccess.Should().BeOfType<PrExpressions.VariableReferenceExpression>();


        }
    }
}