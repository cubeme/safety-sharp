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

namespace SafetySharp.Tests.CSharp
module StatementTransformationTests =

    open System.Linq
    open NUnit.Framework
    open FsUnit
    open SafetySharp.CSharp
    open SafetySharp.Metamodel
    open Microsoft.CodeAnalysis.CSharp.Syntax

    let mutable booleanFieldSymbol = { FieldSymbol.Name = ""; Type = TypeSymbol.Boolean }
    let mutable integerFieldSymbol = { FieldSymbol.Name = ""; Type = TypeSymbol.Integer }

    let transformWithReturnType csharpCode returnType =
        let csharpCode = 
            sprintf "
            class C : Component 
            {
                private bool boolField;
                private int intField;
                %s M()
                {
                    %s;
                }
            }" returnType csharpCode

        let compilation = TestCompilation csharpCode
        let statement = compilation.SyntaxRoot.Descendants<BlockSyntax>().First().Statements.[0]
        let symbolMap = SymbolMap (compilation.CSharpCompilation, [ "C" ])
        booleanFieldSymbol <- symbolMap.Components.[0].Fields.[0]
        integerFieldSymbol <- symbolMap.Components.[0].Fields.[1]

        StatementTransformation.Transform symbolMap compilation.SemanticModel statement

    let transform csharpCode = transformWithReturnType csharpCode "void"

    [<Test>]
    let ``empty statement`` () =
        transform "" |> should equal (EmptyStatement)

    [<Test>]
    let ``statement block`` () =
        let actual = transform "{ boolField = true; intField = 2; }" 
        let assignment1 = (AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), BooleanLiteral true))
        let assignment2 = (AssignmentStatement(FieldAccessExpression(integerFieldSymbol), IntegerLiteral 2))
        let expected = BlockStatement [ assignment1; assignment2 ]

        actual |> should equal expected

    [<Test>]
    let ``stand-alone assignment statement`` () =
        transform "boolField = true" |> should equal (AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), BooleanLiteral true))

    [<Test>]
    let ``assignment statement in binary expression`` () =
        let actual = transform "boolField = true || false"
        let expression = BinaryExpression(BooleanLiteral true, BinaryOperator.LogicalOr, BooleanLiteral false)
        let expected = AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), expression)

        actual |> should equal expected

    [<Test>]
    let ``return statement`` () = 
        transform "return" |> should equal (ReturnStatement None)
        transformWithReturnType "return 1" "int" |> should equal (IntegerLiteral 1 |> Some |> ReturnStatement)
        transformWithReturnType "return false" "bool" |> should equal (BooleanLiteral false |> Some |> ReturnStatement)

    [<Test>]
    let ``guarded commands`` () =
        let ifClause = (BooleanLiteral true, EmptyStatement)
        let elseClause = (UnaryExpression(BooleanLiteral true, UnaryOperator.LogicalNot), ReturnStatement(None))

        transform "if (true) " |> should equal (GuardedCommandStatement [ ifClause ])
        transform "if (true) ; else return" |> should equal (GuardedCommandStatement [ ifClause; elseClause ])

//    [<Test>]
//    let ``ChooseFromValues_FourValues()
//    var actual = Transform("Choose(out intField, -17, 0, 33, 127)")
//
//    var minusSeventeen = new UnaryExpression(new IntegerLiteral(17), UnaryOperator.Minus)
//    var assignment1 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), minusSeventeen)
//    var assignment2 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), new IntegerLiteral(0))
//    var assignment3 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), new IntegerLiteral(33))
//    var assignment4 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), new IntegerLiteral(127))
//
//    var case1 = new GuardedCommandClause(BooleanLiteral.True, assignment1)
//    var case2 = new GuardedCommandClause(BooleanLiteral.True, assignment2)
//    var case3 = new GuardedCommandClause(BooleanLiteral.True, assignment3)
//    var case4 = new GuardedCommandClause(BooleanLiteral.True, assignment4)
//
//    var expected = new GuardedCommandStatement(ImmutableArray.Create(case1, case2, case3, case4))
//    actual.Should().Be(expected)
//
//    [<Test>]
//    let ``ChooseFromValues_TwoValues()
//    var actual = Transform("Choose(out boolField, true, false)")
//
//    var assignment1 = new AssignmentStatement(new FieldAccessExpression(_boolFieldReference), BooleanLiteral.True)
//    var assignment2 = new AssignmentStatement(new FieldAccessExpression(_boolFieldReference), BooleanLiteral.False)
//
//    var case1 = new GuardedCommandClause(BooleanLiteral.True, assignment1)
//    var case2 = new GuardedCommandClause(BooleanLiteral.True, assignment2)
//
//    var expected = new GuardedCommandStatement(ImmutableArray.Create(case1, case2))
//    actual.Should().Be(expected)