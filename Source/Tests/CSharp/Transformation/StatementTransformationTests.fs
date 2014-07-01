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

namespace SafetySharp.Tests.CSharp.Transformation.StatementTransformationTests

open System.Linq
open NUnit.Framework
open SafetySharp.Internal.CSharp
open SafetySharp.Internal.Metamodel
open SafetySharp.Tests
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp.Roslyn
open SafetySharp.Internal.CSharp.Transformation

[<AutoOpen>]
module private StatementTransformationTestsHelper =
    let mutable booleanFieldSymbol = Unchecked.defaultof<FieldSymbol>
    let mutable integerFieldSymbol = Unchecked.defaultof<FieldSymbol>
    let mutable decimalFieldSymbol = Unchecked.defaultof<FieldSymbol>
    let mutable booleanParameterSymbol = Unchecked.defaultof<ParameterSymbol>
    let mutable integerParameterSymbol = Unchecked.defaultof<ParameterSymbol>
    let mutable decimalParameterSymbol = Unchecked.defaultof<ParameterSymbol>
    let mutable booleanLocalSymbol = Unchecked.defaultof<LocalSymbol>
    let mutable integerLocalSymbol = Unchecked.defaultof<LocalSymbol>
    let mutable decimalLocalSymbol = Unchecked.defaultof<LocalSymbol>
    let mutable componentSymbol = Unchecked.defaultof<ComponentSymbol>
    let mutable compilation = null : TestCompilation

    let getMethodSymbol () =
        let getMethodSymbol (ProvidedPort methodSymbol) = methodSymbol 
        getMethodSymbol componentSymbol.ProvidedPorts.[0]

    let transformWithReturnType csharpCode returnType =
        let csharpCode = 
            sprintf "
            class C : Component 
            {
                private bool boolField;
                private int intField;
                private decimal decimalField;
                %s M(bool boolParameter, int intParameter, decimal decimalParameter)
                {
                    bool boolLocal = true;
                    int intLocal = 0;
                    decimal decimalLocal = 0.0m;
                    %s;
                }
            }" returnType csharpCode

        compilation <- TestCompilation csharpCode
        let statement = compilation.SyntaxRoot.Descendants<BlockSyntax>().First().Statements.[3]
        let symbolResolver = SymbolTransformation.TransformComponentSymbols compilation.CSharpCompilation
        componentSymbol <- symbolResolver.ComponentSymbols.[0]

        booleanFieldSymbol <- symbolResolver.ComponentSymbols.[0].Fields.[0]
        integerFieldSymbol <- symbolResolver.ComponentSymbols.[0].Fields.[1]
        decimalFieldSymbol <- symbolResolver.ComponentSymbols.[0].Fields.[2]

        let methodSymbol = getMethodSymbol ()
        booleanParameterSymbol <- methodSymbol.Parameters.[0]
        integerParameterSymbol <- methodSymbol.Parameters.[1]
        decimalParameterSymbol <- methodSymbol.Parameters.[2]

        booleanLocalSymbol <- methodSymbol.Locals.[0]
        integerLocalSymbol <- methodSymbol.Locals.[1]
        decimalLocalSymbol <- methodSymbol.Locals.[2]

        StatementTransformation.Transform symbolResolver compilation.SemanticModel statement

    let transform csharpCode = transformWithReturnType csharpCode "void"

module ``Transform method`` =

    [<Test>]
    let ``empty statement`` () =
        transform "" =? EmptyStatement

    [<Test>]
    let ``statement block`` () =
        let actual = transform "{ boolField = true; intField = 2; }" 
        let assignment1 = WriteField (booleanFieldSymbol, BooleanLiteral true)
        let assignment2 = WriteField (integerFieldSymbol, IntegerLiteral 2)
        let expected = BlockStatement [assignment1; assignment2]

        actual =? expected

    [<Test>]
    let ``stand-alone assignment statement`` () =
        transform "boolField = true" =? WriteField (booleanFieldSymbol, BooleanLiteral true)

    [<Test>]
    let ``assignment statement with binary expression on right-hand side`` () =
        let actual = transform "boolField = true || false"
        let expression = BinaryExpression (BooleanLiteral true, BinaryOperator.LogicalOr, BooleanLiteral false)
        let expected = WriteField (booleanFieldSymbol, expression)

        actual =? expected

    [<Test>]
    let ``field access`` () =
        transform "boolField = boolField" =? WriteField (booleanFieldSymbol, ReadField (booleanFieldSymbol, None))
        transform "intField = intField" =? WriteField (integerFieldSymbol, ReadField (integerFieldSymbol, None))
        transform "decimalField = decimalField" =? WriteField (decimalFieldSymbol, ReadField (decimalFieldSymbol, None))

    [<Test>]
    let ``parameter access`` () =
        transform "boolParameter = boolParameter" =? WriteParameter (booleanParameterSymbol, ReadParameter booleanParameterSymbol)
        transform "intParameter = intParameter" =? WriteParameter (integerParameterSymbol, ReadParameter integerParameterSymbol)
        transform "decimalParameter = decimalParameter" =? WriteParameter (decimalParameterSymbol, ReadParameter decimalParameterSymbol)

    [<Test>]
    let ``local access`` () =
        transform "boolLocal = boolLocal" =? WriteLocal (booleanLocalSymbol, ReadLocal booleanLocalSymbol)
        transform "intLocal = intLocal" =? WriteLocal (integerLocalSymbol, ReadLocal integerLocalSymbol)
        transform "decimalLocal = decimalLocal" =? WriteLocal (decimalLocalSymbol, ReadLocal decimalLocalSymbol)

    [<Test>]
    let ``skips over declarations of local variables without an initializer`` () =
        transform "{ bool x; int y; return; }" =? BlockStatement [BlockStatement []; BlockStatement []; ReturnStatement None]
        transform "{ bool x, y; return; }" =? BlockStatement [BlockStatement []; ReturnStatement None]

    [<Test>]
    let ``initializers of local variables`` () =
        let actual = transform "{ var x = true; var y = 0 + 3; return; }"
        let methodSymbol = getMethodSymbol ()
        let x = WriteLocal (methodSymbol.Locals.[3], BooleanLiteral true)
        let y = WriteLocal (methodSymbol.Locals.[4], BinaryExpression (IntegerLiteral 0, BinaryOperator.Add, IntegerLiteral 3))
        let expected = BlockStatement [BlockStatement [x]; BlockStatement [y]; ReturnStatement None]
        actual =? expected

        let actual = transform "{ int x = 1, y = 2; return; }"
        let methodSymbol = getMethodSymbol ()
        let x = WriteLocal (methodSymbol.Locals.[3], IntegerLiteral 1)
        let y = WriteLocal (methodSymbol.Locals.[4], IntegerLiteral 2)
        let expected = BlockStatement [BlockStatement [x; y]; ReturnStatement None]
        actual =? expected

    [<Test>]
    let ``return statement`` () = 
        transform "return" =? ReturnStatement None
        transformWithReturnType "return 1" "int" =? (IntegerLiteral 1 |> Some |> ReturnStatement)
        transformWithReturnType "return false" "bool" =? (BooleanLiteral false |> Some |> ReturnStatement)

    [<Test>]
    let ``single if-then-else statement`` () =
        let ifClause = (BooleanLiteral true, EmptyStatement)
        let elseClause = (UnaryExpression(BooleanLiteral true, UnaryOperator.LogicalNot), ReturnStatement(None))

        transform "if (true) " =? GuardedCommandStatement [ ifClause ]
        transform "if (true) ; else return" =? GuardedCommandStatement [ ifClause; elseClause ]

    [<Test>]
    let ``nested if-then-else statements`` () =
        let actual = transform "if (boolField) intField = 1; else if (intField > 2) decimalField = 3.14m; else { boolField = false; intField = 2; }"
        let ifCondition = ReadField (booleanFieldSymbol, None)
        let ifStatement = WriteField (integerFieldSymbol, IntegerLiteral 1)
        let ifClause = (ifCondition, ifStatement)
        let elseIfCondition = BinaryExpression (ReadField (integerFieldSymbol, None), BinaryOperator.GreaterThan, IntegerLiteral 2)
        let elseIfStatement = WriteField (decimalFieldSymbol, DecimalLiteral 3.14m)
        let elseIfClause = (elseIfCondition, elseIfStatement)
        let elseStatement1 = WriteField (booleanFieldSymbol, BooleanLiteral false)
        let elseStatement2 = WriteField (integerFieldSymbol, IntegerLiteral 2)
        let elseStatements = BlockStatement [elseStatement1; elseStatement2]
        let elseClause = (UnaryExpression (elseIfCondition, UnaryOperator.LogicalNot), elseStatements)
        let nestedGuardedCommand = GuardedCommandStatement [elseIfClause; elseClause]
        let expected = GuardedCommandStatement [ifClause; (UnaryExpression (ifCondition, UnaryOperator.LogicalNot), nestedGuardedCommand)]

        actual =? expected

    [<Test>]
    let ``choose Boolean value`` () =
        let actual = transform "Choose.Boolean(out boolField)"

        let assignment1 = WriteField (booleanFieldSymbol, BooleanLiteral true)
        let assignment2 = WriteField (booleanFieldSymbol, BooleanLiteral false)

        let expected = GuardedCommandStatement [(BooleanLiteral true, assignment1); (BooleanLiteral true, assignment2)]
        actual =? expected

    [<Test>]
    let ``choose integer value`` () =
        let actual = transform "Choose.Value(out intField, -17, 0, 33, 127)"

        let minusSeventeen = UnaryExpression(IntegerLiteral 17, UnaryOperator.Minus)
        let assignment1 = WriteField (integerFieldSymbol, minusSeventeen)
        let assignment2 = WriteField (integerFieldSymbol, IntegerLiteral 0)
        let assignment3 = WriteField (integerFieldSymbol, IntegerLiteral 33)
        let assignment4 = WriteField (integerFieldSymbol, IntegerLiteral 127)

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
        let assignment1 = WriteField (decimalFieldSymbol, minusSeventeen)
        let assignment2 = WriteField (decimalFieldSymbol, DecimalLiteral 0m)
        let assignment3 = WriteField (decimalFieldSymbol, DecimalLiteral 33.4m)
        let assignment4 = WriteField (decimalFieldSymbol, DecimalLiteral 127.23m)

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

    let private transform csharpCode =
        compilation <- TestCompilation csharpCode
        symbolResolver <- SymbolTransformation.TransformComponentSymbols compilation.CSharpCompilation

        StatementTransformation.TransformMethodBodies compilation.CSharpCompilation symbolResolver

    [<Test>]
    let ``does not try to transform extern method (required port)`` () =
        let actual = transform "class A : Component { extern void M(); }"
        let classSymbol = compilation.FindClassSymbol "A"
        let componentSymbol = symbolResolver.ResolveComponent classSymbol
        let expected = [(componentSymbol, componentSymbol.UpdateMethod), EmptyStatement] |> Map.ofList
        actual =? expected
    
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
                (componentSymbol, methodSymbol), statement
                (componentSymbol, componentSymbol.UpdateMethod), EmptyStatement
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
        let expected = [(componentSymbol, methodSymbol), statement] |> Map.ofList
        
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
                (componentSymbolA, componentSymbolA.UpdateMethod), statement
                (componentSymbolB, componentSymbolB.UpdateMethod), statement
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
                (componentSymbolA, methodSymbolUpdate), statement3
                (componentSymbolA, methodSymbolM), statement1
                (componentSymbolB, methodSymbolN), statement2
                (componentSymbolB, componentSymbolB.UpdateMethod), statement3
            ] |> Map.ofList
        
        actual =? expected