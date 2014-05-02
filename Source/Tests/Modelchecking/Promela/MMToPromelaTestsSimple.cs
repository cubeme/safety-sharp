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

            //var fieldSymbol = _compilation.FindFieldSymbol("BooleanComponent", "_value");
            //var fieldReference = _symbolMap.GetFieldReference(fieldSymbol);

            //f
            var fieldReference = new MM.MetamodelReference<MMDeclarations.FieldDeclaration>();

            var field = new MMDeclarations.FieldDeclaration(new MM.Identifier("_value"), MMTypeReferences.TypeReference.Boolean);

            var assignment1 = new MMStatements.AssignmentStatement(new MMExpressions.FieldAccessExpression(fieldReference), MMExpressions.BooleanLiteral.True);
            var assignment2 = new MMStatements.AssignmentStatement(new MMExpressions.FieldAccessExpression(fieldReference), MMExpressions.BooleanLiteral.False);

            var clause1 = new MMStatements.GuardedCommandClause(MMExpressions.BooleanLiteral.True, assignment1);
            var clause2 = new MMStatements.GuardedCommandClause(MMExpressions.BooleanLiteral.True, assignment2);

            var updateBody = new MMStatements.GuardedCommandStatement(ImmutableArray.Create(clause1, clause2));
            var updateMethod = new MMDeclarations.MethodDeclaration(new MM.Identifier("Update"), updateBody.AsBlockStatement());

            var mmsimple = new MMDeclarations.ComponentDeclaration(new MM.Identifier("BooleanComponent"),
                                                    updateMethod,
                                                    ImmutableArray<MMDeclarations.MethodDeclaration>.Empty,
                                                    ImmutableArray.Create(field));


            
        }
    }
}