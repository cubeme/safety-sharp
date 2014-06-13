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

namespace SafetySharp.Tests.CSharp.StatementTransformationTests

open System.Linq
open NUnit.Framework
open Swensen.Unquote
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Tests
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp.Extensions
open SafetySharp.CSharp.Transformation

[<AutoOpen>]
module private StatementTransformationTestsHelper =
    let mutable booleanFieldSymbol = { FieldSymbol.Name = ""; Type = TypeSymbol.Boolean }
    let mutable integerFieldSymbol = { FieldSymbol.Name = ""; Type = TypeSymbol.Integer }
    let mutable decimalFieldSymbol = { FieldSymbol.Name = ""; Type = TypeSymbol.Decimal }

    let transformWithReturnType csharpCode returnType =
        let csharpCode = 
            sprintf "
            class C : Component 
            {
                private bool boolField;
                private int intField;
                private decimal decimalField;
                %s M()
                {
                    %s;
                }
            }" returnType csharpCode

        let compilation = TestCompilation csharpCode
        let statement = compilation.SyntaxRoot.Descendants<BlockSyntax>().First().Statements.[0]
        let symbolResolver = SymbolTransformation.Transform compilation.CSharpCompilation
        booleanFieldSymbol <- symbolResolver.ComponentSymbols.[0].Fields.[0]
        integerFieldSymbol <- symbolResolver.ComponentSymbols.[0].Fields.[1]
        decimalFieldSymbol <- symbolResolver.ComponentSymbols.[0].Fields.[2]

        StatementTransformation.Transform symbolResolver compilation.SemanticModel statement

    let transform csharpCode = transformWithReturnType csharpCode "void"

module ``Transform method`` =

    [<Test>]
    let ``empty statement`` () =
        transform "" =? EmptyStatement

    [<Test>]
    let ``statement block`` () =
        let actual = transform "{ boolField = true; intField = 2; }" 
        let assignment1 = (AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), BooleanLiteral true))
        let assignment2 = (AssignmentStatement(FieldAccessExpression(integerFieldSymbol), IntegerLiteral 2))
        let expected = BlockStatement [ assignment1; assignment2 ]

        actual =? expected

    [<Test>]
    let ``stand-alone assignment statement`` () =
        transform "boolField = true" =? AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), BooleanLiteral true)

    [<Test>]
    let ``assignment statement in binary expression`` () =
        let actual = transform "boolField = true || false"
        let expression = BinaryExpression(BooleanLiteral true, BinaryOperator.LogicalOr, BooleanLiteral false)
        let expected = AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), expression)

        actual =? expected

    [<Test>]
    let ``return statement`` () = 
        transform "return" =? ReturnStatement None
        transformWithReturnType "return 1" "int" =? (IntegerLiteral 1 |> Some |> ReturnStatement)
        transformWithReturnType "return false" "bool" =? (BooleanLiteral false |> Some |> ReturnStatement)

    [<Test>]
    let ``guarded commands`` () =
        let ifClause = (BooleanLiteral true, EmptyStatement)
        let elseClause = (UnaryExpression(BooleanLiteral true, UnaryOperator.LogicalNot), ReturnStatement(None))

        transform "if (true) " =? GuardedCommandStatement [ ifClause ]
        transform "if (true) ; else return" =? GuardedCommandStatement [ ifClause; elseClause ]

    [<Test>]
    let ``choose Boolean value`` () =
        let actual = transform "Choose.Boolean(out boolField)"

        let assignment1 = AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), BooleanLiteral true)
        let assignment2 = AssignmentStatement(FieldAccessExpression(booleanFieldSymbol), BooleanLiteral false)

        let expected = GuardedCommandStatement [(BooleanLiteral true, assignment1); (BooleanLiteral true, assignment2)]
        actual =? expected

    [<Test>]
    let ``choose integer value`` () =
        let actual = transform "Choose.Value(out intField, -17, 0, 33, 127)"

        let minusSeventeen = UnaryExpression(IntegerLiteral 17, UnaryOperator.Minus)
        let assignment1 = AssignmentStatement(FieldAccessExpression(integerFieldSymbol), minusSeventeen)
        let assignment2 = AssignmentStatement(FieldAccessExpression(integerFieldSymbol), IntegerLiteral 0)
        let assignment3 = AssignmentStatement(FieldAccessExpression(integerFieldSymbol), IntegerLiteral 33)
        let assignment4 = AssignmentStatement(FieldAccessExpression(integerFieldSymbol), IntegerLiteral 127)

        let expected = 
            GuardedCommandStatement [
                (BooleanLiteral true, assignment1)
                (BooleanLiteral true, assignment2)
                (BooleanLiteral true, assignment3)
                (BooleanLiteral true, assignment4) 
            ]

        actual =? expected

    [<Test>]
    let ``choose decimal value`` () =
        let actual = transform "Choose.Value(out decimalField, -17.0m, 0.0m, 33.4m, 127.23m)"

        let minusSeventeen = UnaryExpression(DecimalLiteral 17.0m, UnaryOperator.Minus)
        let assignment1 = AssignmentStatement(FieldAccessExpression(decimalFieldSymbol), minusSeventeen)
        let assignment2 = AssignmentStatement(FieldAccessExpression(decimalFieldSymbol), DecimalLiteral 0m)
        let assignment3 = AssignmentStatement(FieldAccessExpression(decimalFieldSymbol), DecimalLiteral 33.4m)
        let assignment4 = AssignmentStatement(FieldAccessExpression(decimalFieldSymbol), DecimalLiteral 127.23m)

        let expected = 
            GuardedCommandStatement [
                (BooleanLiteral true, assignment1)
                (BooleanLiteral true, assignment2)
                (BooleanLiteral true, assignment3)
                (BooleanLiteral true, assignment4) 
            ]

        actual =? expected

module ``TransformMethodBodies method`` =
    let mutable private compilation = Unchecked.defaultof<TestCompilation>
    let mutable private symbolResolver = Unchecked.defaultof<SymbolResolver>

    let transform csharpCode =
        compilation <- TestCompilation csharpCode
        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation

        StatementTransformation.TransformMethodBodies compilation.CSharpCompilation symbolResolver
    
    [<Test>]
    let ``transforms body of single method of single component`` () =
        let expression = BinaryExpression (BooleanLiteral true, LogicalOr, BinaryExpression (IntegerLiteral 1, Equals, IntegerLiteral 2))
        let statement = BlockStatement [ReturnStatement <| Some expression]
        let actual = transform "class A : Component { bool M() { return true || 1 == 2; }}"
        let classSymbol = compilation.FindClassSymbol "A"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol
        let csharpMethodSymbol = compilation.FindMethodSymbol "A" "M"
        let methodSymbol = symbolResolver.ResolveMethod csharpMethodSymbol
        let expected = 
            [
                ((componentSymbol, methodSymbol), statement)
                ((componentSymbol, componentSymbol.UpdateMethod), EmptyStatement)
            ] |> Map.ofList
        
        actual =? expected

    [<Test>]
    let ``transforms body of update method of a component`` () =
        let statement = BlockStatement [ReturnStatement None]
        let actual = transform "class A : Component { public override void Update() { return; }}"
        let classSymbol = compilation.FindClassSymbol "A"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol
        let csharpMethodSymbol = compilation.FindMethodSymbol "A" "Update"
        let methodSymbol = symbolResolver.ResolveMethod csharpMethodSymbol
        let expected = [((componentSymbol, methodSymbol), statement)] |> Map.ofList
        
        actual =? expected

    [<Test>]
    let ``transforms inherited body of update method of a component`` () =
        let statement = BlockStatement [ReturnStatement None]
        let actual = transform "class A : Component { public override void Update() { return; }} class B : A {}"
        let classSymbolA = compilation.FindClassSymbol "A"
        let classSymbolB = compilation.FindClassSymbol "B"
        let componentSymbolA = symbolResolver.ResolveComponent classSymbolA
        let componentSymbolB = symbolResolver.ResolveComponent classSymbolB
        let expected = 
            [
                ((componentSymbolA, componentSymbolA.UpdateMethod), statement)
                ((componentSymbolB, componentSymbolB.UpdateMethod), statement)
            ] |> Map.ofList
        
        actual =? expected

    [<Test>]
    let ``transforms bodies of multiple methods of multiple components`` () =
        let expression = BinaryExpression (BooleanLiteral true, LogicalOr, BinaryExpression (IntegerLiteral 1, Equals, IntegerLiteral 2))
        let statement1 = BlockStatement [ReturnStatement <| Some expression]
        let statement2 = BlockStatement []
        let statement3 = BlockStatement [ReturnStatement None]

        let actual = transform "class A : Component { public override void Update() { return; } bool M() { return true || 1 == 2; }} class B : A { void N() {}}"

        let classSymbolA = compilation.FindClassSymbol "A"
        let classSymbolB = compilation.FindClassSymbol "B"

        let componentSymbolA = symbolResolver.ResolveComponent classSymbolA
        let componentSymbolB = symbolResolver.ResolveComponent classSymbolB

        let csharpMethodSymbolUpdate = compilation.FindMethodSymbol "A" "Update"
        let csharpMethodSymbolM = compilation.FindMethodSymbol "A" "M"
        let csharpMethodSymbolN = compilation.FindMethodSymbol "B" "N"

        let methodSymbolUpdate = symbolResolver.ResolveMethod csharpMethodSymbolUpdate
        let methodSymbolM = symbolResolver.ResolveMethod csharpMethodSymbolM
        let methodSymbolN = symbolResolver.ResolveMethod csharpMethodSymbolN

        let expected = 
            [
                ((componentSymbolA, methodSymbolUpdate), statement3)
                ((componentSymbolA, methodSymbolM), statement1)
                ((componentSymbolB, methodSymbolN), statement2)
                ((componentSymbolB, componentSymbolB.UpdateMethod), statement3)
            ] |> Map.ofList
        
        actual =? expected