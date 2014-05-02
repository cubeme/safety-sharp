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
    using System.Collections.Immutable;
    using NUnit.Framework;
    using MM = SafetySharp.Metamodel;
    using MMExpressions = SafetySharp.Metamodel.Expressions;
    using MMStatements = SafetySharp.Metamodel.Statements;
    using MMTypeReferences = SafetySharp.Metamodel.TypeReferences;
    using MMDeclarations = SafetySharp.Metamodel.Declarations;
    using MMInstances = SafetySharp.Metamodel.Instances;
    using PrExpression = SafetySharp.Modelchecking.Promela.Expressions.Expression;
    using PrStatement = SafetySharp.Modelchecking.Promela.Statements.Statement;

    [TestFixture]
    public class MMToPromelaTestsSimple
    {
        // https://bitbucket.org/Axel777/safetysharp/src/2e0a77c3a9088567a878698a50c0f563eb58eb25/Source/Tests/Tests.cs?at=master

        [Test]
        public void Test()
        {
            var stateVar = new MMDeclarations.StateVariableDeclaration(new MM.Identifier("x"), MMTypeReferences.TypeReference.Boolean);

            var guardedCommand = new MMStatements.GuardedCommandStatement(
                ImmutableArray.Create(
                                      new MMStatements.GuardedCommandClause(
                                          new MMExpressions.BooleanLiteral(true),
                                          new MMStatements.AssignmentStatement(new MMExpressions.StateVariableExpression(stateVar), MMExpressions.BooleanLiteral.True)),
                                      new MMStatements.GuardedCommandClause(
                                          new MMExpressions.BooleanLiteral(true),
                                          new MMStatements.AssignmentStatement(new MMExpressions.StateVariableExpression(stateVar), MMExpressions.BooleanLiteral.True))
                    ));

            var componentDeclaration = new MMDeclarations.ComponentDeclaration(
                name: new MM.Identifier("Test"),
                @namespace: "Test",
                methods: ImmutableArray.Create<MMDeclarations.MemberDeclaration>(stateVar),
                updateStatement: guardedCommand);

            var instance = new MMInstances.ComponentInstance();


            ((MMDeclarations.StateVariableDeclaration)component.Members[0]).Name.Name.Should().Be("x");
        }
    }
}