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

namespace Tests
{
	using System;
	using System.Collections.Immutable;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Instances;
	using SafetySharp.Metamodel.Statements;
	using SafetySharp.Metamodel.TypeReferences;

	[TestFixture]
	public class EnumTests
	{
		//[Test]
		//public void Test()
		//{
		//	var guardedCommand = new GuardedCommandExpression(
		//		ImmutableArray.Create(
		//							  new GuardedCommandClause(
		//								  new BooleanLiteral(true),
		//								  new ReturnStatement(BooleanLiteral.True)),
		//							  new GuardedCommandClause(
		//								  new BooleanLiteral(true),
		//								  new ReturnStatement(BooleanLiteral.False))
		//			));

		//	var stateVar = new StateVariableDeclaration(new Identifier("x"), TypeReference.Boolean);
		//	var statement = new ExpressionStatement(
		//		new AssignmentExpression(
		//			new StateVariableExpression(stateVar), guardedCommand)
		//		);

		//	var component = new ComponentDeclaration(
		//		name: new Identifier("Test"),
		//		@namespace: "Test",
		//		members: ImmutableArray.Create<MemberDeclaration>(stateVar),
		//		updateStatement: statement);

		//	var instance = new ComponentInstance(ImmutableArray.Create<Expression>(guardedCommand));
		//	((StateVariableDeclaration)component.Members[0]).Name.Name.Should().Be("x");

		//	var rewriter = new MyRewriter();
		//	var component2 = component.Accept(rewriter) as ComponentDeclaration;
		//}

		//class MyRewriter : MetamodelRewriter
		//{
		//	/// <summary>
		//	///     Rewrites a metamodel element of type <see cref="GuardedCommandExpression" />.
		//	/// </summary>
		//	/// <param name="guardedCommandExpression">The <see cref="GuardedCommandExpression" /> instance that should be rewritten.</param>
		//	public override MetamodelElement VisitGuardedCommandExpression(GuardedCommandExpression guardedCommandExpression)
		//	{
		//		return new GuardedCommandExpression(ImmutableArray<GuardedCommandClause>.Empty);
		//	}
		//}
	}
}