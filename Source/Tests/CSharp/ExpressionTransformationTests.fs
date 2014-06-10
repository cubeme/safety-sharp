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

namespace SafetySharp.Tests
module ExpressionTransformationTests =

    open System.Linq
    open NUnit.Framework
    open FsUnit
    open SafetySharp.CSharp
    open SafetySharp.Metamodel
    open Microsoft.CodeAnalysis.CSharp.Syntax

    let transform csharpCode =
        let csharpCode = "
            class C : Component 
            {
                private bool boolField; 
                private int intField;
                void M()
                {
                    var x = " + csharpCode + ";
                }
            }"

        let compilation = new TestCompilation(csharpCode);
        let expression = compilation.SyntaxRoot.DescendantNodes().OfType<EqualsValueClauseSyntax>().Single().Value;

        Transformation.TransformExpression expression

    [<Test>]
    let ``boolean literals`` () =
        transform "false" |> should equal (BooleanLiteral false)
        transform "true" |> should equal (BooleanLiteral true)

    [<Test>]
    let ``integer literals`` () =
       transform "0" |> should equal (IntegerLiteral 0)
       transform "1" |> should equal (IntegerLiteral 1)
       transform "10" |> should equal (IntegerLiteral 10)
       transform "41223" |> should equal (IntegerLiteral 41223)

    [<Test>]
    let ``decimal literals`` () =
        transform "0m" |> should equal (DecimalLiteral 0m)
        transform "10m" |> should equal (DecimalLiteral 10m)
        transform "0.5m" |> should equal (DecimalLiteral 0.5m)
        transform "17.412m" |> should equal (DecimalLiteral 17.412m)

    [<Test>]
    let ``minus expressions`` () =
        transform "-.50m" |> should equal (UnaryExpression(DecimalLiteral(0.50m), UnaryOperator.Minus));
        transform "-10m" |> should equal (UnaryExpression(DecimalLiteral(10m), UnaryOperator.Minus));
        transform "-4" |> should equal (UnaryExpression(IntegerLiteral(4), UnaryOperator.Minus));
        transform "-0" |> should equal (UnaryExpression(IntegerLiteral(0), UnaryOperator.Minus));

    [<Test>]
    let ``not expressions`` () =
        transform "!true" |> should equal (UnaryExpression(BooleanLiteral true, UnaryOperator.LogicalNot));
        transform "!false" |> should equal (UnaryExpression(BooleanLiteral false, UnaryOperator.LogicalNot));

    [<Test>]
    let ``nested unary expressions`` () =
        transform "-+1" |> should equal (UnaryExpression(IntegerLiteral(1), UnaryOperator.Minus));
        transform "!!true" |> should equal (UnaryExpression(UnaryExpression(BooleanLiteral true, UnaryOperator.LogicalNot), UnaryOperator.LogicalNot))

    [<Test>]
    let ``plus expressions`` () =
        transform "+.50m" |> should equal (DecimalLiteral(0.50m));
        transform "+10m" |> should equal (DecimalLiteral(10m));
        transform "+4" |> should equal (IntegerLiteral(4));
        transform "+0" |> should equal (IntegerLiteral(0));

    [<Test>]
    let ``add expressions`` () =
        transform "1 + 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.Add, IntegerLiteral 1))
        transform "13m + 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.Add, DecimalLiteral 17.2m))

    [<Test>]
    let ``subtract expressions`` () =
        transform "1 - 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.Subtract, IntegerLiteral 1))
        transform "13m - 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.Subtract, DecimalLiteral 17.2m))

    [<Test>]
    let ``multiply expressions`` () =
        transform "1 * 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.Multiply, IntegerLiteral 1))
        transform "13m * 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.Multiply, DecimalLiteral 17.2m))

    [<Test>]
    let ``divide expressions`` () =
        transform "1 / 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.Divide, IntegerLiteral 1))
        transform "13m / 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.Divide, DecimalLiteral 17.2m))

    [<Test>]
    let ``modulo expressions`` () =
        transform "1 % 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.Modulo, IntegerLiteral 1))
        transform "13m %17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.Modulo, DecimalLiteral 17.2m))

    [<Test>]
    let ``equal expressions`` () =
        transform "1 == 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.Equals, IntegerLiteral 1))
        transform "13m == 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.Equals, DecimalLiteral 17.2m))

    [<Test>]
    let ``not equal expressions`` () =
        transform "1 != 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.NotEquals, IntegerLiteral 1))
        transform "13m != 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.NotEquals, DecimalLiteral 17.2m))

    [<Test>]
    let ``greater than expressions`` () =
        transform "1 > 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.GreaterThan, IntegerLiteral 1))
        transform "13m > 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.GreaterThan, DecimalLiteral 17.2m))

    [<Test>]
    let ``greater than or equal expressions`` () =
        transform "1 >= 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.GreaterThanOrEqual, IntegerLiteral 1))
        transform "13m >= 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.GreaterThanOrEqual, DecimalLiteral 17.2m))

    [<Test>]
    let ``less than expressions`` () =
        transform "1 < 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.LessThan, IntegerLiteral 1))
        transform "13m < 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.LessThan, DecimalLiteral 17.2m))

    [<Test>]
    let ``less than or equal expressions`` () =
        transform "1 <= 1" |> should equal (BinaryExpression (IntegerLiteral 1, BinaryOperator.LessThanOrEqual, IntegerLiteral 1))
        transform "13m <= 17.2m" |> should equal (BinaryExpression (DecimalLiteral 13m, BinaryOperator.LessThanOrEqual, DecimalLiteral 17.2m))

    [<Test>]
    let ``logical and expressions`` () =
        transform "false && true" |> should equal (BinaryExpression (BooleanLiteral false, BinaryOperator.LogicalAnd, BooleanLiteral true))
        transform "true && true" |> should equal (BinaryExpression (BooleanLiteral true, BinaryOperator.LogicalAnd, BooleanLiteral true))

    [<Test>]
    let ``logical or expressions`` () =
        transform "false || true" |> should equal (BinaryExpression (BooleanLiteral false, BinaryOperator.LogicalOr, BooleanLiteral true))
        transform "true || true" |> should equal (BinaryExpression (BooleanLiteral true, BinaryOperator.LogicalOr, BooleanLiteral true))

//    [<Test>]
//    let ``field access expressions`` () =
//        transform "boolField").Should () =.Be(new FieldAccessExpression(_fieldReference));

//    [<Test>]
//    let ``field access in binary expression`` () =
//    transform "boolField == false")
//    .Should () =.Be(new BinaryExpression(new FieldAccessExpression(_fieldReference), BinaryOperator.Equals, BooleanLiteral.False));

    [<Test>]
    let ``nested binary expressions`` () =
        let add = BinaryExpression(IntegerLiteral(1), BinaryOperator.Add, IntegerLiteral(2));
        let multiply = BinaryExpression(add, BinaryOperator.Multiply, IntegerLiteral(10));
        transform "(1 + 2) * 10" |> should equal multiply

        let multiply = BinaryExpression(IntegerLiteral(1), BinaryOperator.Multiply, IntegerLiteral(10));
        let add = BinaryExpression(multiply, BinaryOperator.Add, IntegerLiteral(2));
        transform "1 * 10 + 2" |> should equal add

        let left = BinaryExpression(IntegerLiteral(1), BinaryOperator.Add, IntegerLiteral(2));
        let right = BinaryExpression(IntegerLiteral(4), BinaryOperator.Add, IntegerLiteral(5));
        let multiply = BinaryExpression(left, BinaryOperator.Multiply, right);
        transform "(1 + 2) * (4 + 5)" |> should equal multiply

    [<Test>]
    let ``nested unary and binary expressions`` () =
        let minusOne = UnaryExpression(IntegerLiteral(1), UnaryOperator.Minus);
        let left = BinaryExpression(minusOne, BinaryOperator.Add, IntegerLiteral(2));
        let right = BinaryExpression(IntegerLiteral(4), BinaryOperator.Add, IntegerLiteral(5));
        let multiply = BinaryExpression(UnaryExpression(left, UnaryOperator.Minus), BinaryOperator.Multiply, right);

        transform "-(-1 + 2) * (4 + +5)" |> should equal multiply
