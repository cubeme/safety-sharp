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

namespace SafetySharp.Tests.CSharp.Transformation.FormulaTransformationTests

open System
open System.Linq
open NUnit.Framework
open Swensen.Unquote
open SafetySharp.Internal.CSharp
open SafetySharp.Internal.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp
open SafetySharp.Tests
open SafetySharp.Internal.CSharp.Transformation

[<AutoOpen>]
module private FormulaTransformationTestsHelper =
    let mutable symbolResolver = Unchecked.defaultof<SymbolResolver>
    let mutable objectResolver = Unchecked.defaultof<ObjectResolver>
    let mutable unknownComponent : IComponent = null

    let compile formulaType csharpCode =
        let compilation = TestCompilation (@"
            enum E { A, B, C }
            class A : Component { public bool boolField; private int intField; }
            class B : Component { public B(A a) { this.a = a; } private A a; public bool boolField; }
            class M : Model {
                public M() {
                    var a = new A();
                    var sub = new A();
                    var b = new B(sub);
                    Unknown = new A();

                    var enumValue = E.B;
                    int intValue = 17;
                    bool boolValue = true;

                    var accessIntField = a.Access<int>(""intField"");
                    var unknownAccess = Unknown.Access<bool>(""boolField"");

                    Formula = " + csharpCode + ";

                    SetPartitions(a, b);
                }

                public A Unknown;
                public " + formulaType + " Formula;
            }")
        
        let model = compilation.CreateObject<Model> "M"
        model.FinalizeMetadata ()
        symbolResolver <- SymbolTransformation.Transform compilation.CSharpCompilation model
        objectResolver <- ObjectTransformation.Transform model symbolResolver
        unknownComponent <- model.GetType().GetField("Unknown").GetValue model :?> Component
        model.GetType().GetField("Formula").GetValue model

    let transform formula =
        FormulaTransformation.Transform symbolResolver objectResolver formula

    let compileLtl csharpCode = 
        let formula = compile "LtlFormula" csharpCode
        transform (formula :?> LtlFormula).Formula

    let compileCtl csharpCode = 
        let formula = compile "CtlFormula" csharpCode
        transform (formula :?> CtlFormula).Formula

    let raisesUnknownComponent expression = 
        raisesWith<UnknownComponentException> expression (fun e -> <@ e.UnknownComponent = unknownComponent @>)

[<TestFixture>]
module ``Linear Temporal Logic`` =
    [<Test>]
    let ``throws when unknown component instance is accessed directly`` () =
        raisesUnknownComponent <@ compileLtl "Ltl.StateExpression(() => !Unknown.boolField)" @>

    [<Test>]
    let ``throws when unknown component instance is accessed indirectly`` () =
        raisesUnknownComponent <@ compileLtl "Ltl.StateExpression(() => !unknownAccess)" @>

    [<Test>]
    let ``transform state expression`` () =
        let oneEqualsSeventeen = BinaryExpression (IntegerLiteral 1, BinaryOperator.Equals, IntegerLiteral 17)
        let expected = StateFormula (BinaryExpression (BooleanLiteral true, BinaryOperator.LogicalOr, oneEqualsSeventeen))
        compileLtl "Ltl.StateExpression(() => true || 1 == intValue)" =? expected

    [<Test>]
    let ``transform enum literals in state expressions`` () =
        let expected = StateFormula (BinaryExpression (IntegerLiteral 1, BinaryOperator.Equals, IntegerLiteral 2))
        compileLtl "Ltl.StateExpression(() => enumValue == E.C)" =? expected

    [<Test>]
    let ``transform component indirect member access`` () =
        let actual = compileLtl "Ltl.StateExpression(() => accessIntField == intValue)"
        let fieldAccess = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[1], Some symbolResolver.ModelSymbol.ComponentObjects.[0])
        let expected = StateFormula (BinaryExpression (fieldAccess, BinaryOperator.Equals, IntegerLiteral 17))
        actual =? expected

    [<Test>]
    let ``transform component direct member access`` () =
        let actual = compileLtl "Ltl.StateExpression(() => !a.boolField)"
        let fieldAccess = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[0])
        let expected = StateFormula (UnaryExpression (fieldAccess, UnaryOperator.LogicalNot))
        actual =? expected

    [<Test>]
    let ``transform subcomponent direct member access`` () =
        let actual = compileLtl "Ltl.StateExpression(() => !sub.boolField)"
        let fieldAccess = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[2])
        let expected = StateFormula (UnaryExpression (fieldAccess, UnaryOperator.LogicalNot))
        actual =? expected

    [<Test>]
    let ``transform mixed component member access`` () =
        let actual = compileLtl "Ltl.StateExpression(() => a.boolField != b.boolField)"
        let fieldAccessA = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[0])
        let fieldAccessB = ReadField (symbolResolver.ComponentSymbols.[1].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[1])
        let expected = StateFormula (BinaryExpression (fieldAccessA, BinaryOperator.NotEquals, fieldAccessB))
        actual =? expected

    [<Test>]
    let ``transform next`` () =
        let expression = BinaryExpression (IntegerLiteral 17, BinaryOperator.GreaterThan, IntegerLiteral 89)
        compileLtl "Ltl.Next(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.Next)

        compileLtl "Ltl.Next(Ltl.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.Next), UnaryFormulaOperator.Next)

    [<Test>]
    let ``transform finally`` () =
        let expression = BinaryExpression (IntegerLiteral 17, BinaryOperator.GreaterThan, IntegerLiteral 89)
        compileLtl "Ltl.Finally(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.Finally)

        compileLtl "Ltl.Finally(Ltl.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.Next), UnaryFormulaOperator.Finally)

    [<Test>]
    let ``transform globally`` () =
        let expression = BinaryExpression (IntegerLiteral 17, BinaryOperator.GreaterThan, IntegerLiteral 89)
        compileLtl "Ltl.Globally(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.Globally)

        compileLtl "Ltl.Globally(Ltl.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.Next), UnaryFormulaOperator.Globally)

    [<Test>]
    let ``transform until`` () =
        let stateFormula = StateFormula (BooleanLiteral true)
        let nextFormula = UnaryFormula (stateFormula, UnaryFormulaOperator.Next)

        compileLtl "Ltl.Until(() => boolValue, () => boolValue)" =? 
            BinaryFormula(stateFormula, BinaryFormulaOperator.Until, stateFormula)

        compileLtl "Ltl.Until(Ltl.Next(() => boolValue), () => boolValue)" =? 
            BinaryFormula(nextFormula, BinaryFormulaOperator.Until, stateFormula)

        compileLtl "Ltl.Until(() => boolValue, Ltl.Next(() => boolValue))" =? 
            BinaryFormula(stateFormula, BinaryFormulaOperator.Until, nextFormula)

        compileLtl "Ltl.Until(Ltl.Next(() => boolValue), Ltl.Next(() => boolValue))" =? 
            BinaryFormula(nextFormula, BinaryFormulaOperator.Until, nextFormula)

[<TestFixture>]
module ``Computation Tree Logic`` =
    [<Test>]
    let ``throws when unknown component instance is accessed directly`` () =
        raisesUnknownComponent <@ compileCtl "Ctl.StateExpression(() => !Unknown.boolField)" @>

    [<Test>]
    let ``throws when unknown component instance is accessed indirectly`` () =
        raisesUnknownComponent <@ compileCtl "Ctl.StateExpression(() => !unknownAccess)" @>

    [<Test>]
    let ``transform state expression`` () =
        let oneEqualsSeventeen = BinaryExpression(IntegerLiteral 1, BinaryOperator.Equals, IntegerLiteral 17)
        let expected =  StateFormula(BinaryExpression(BooleanLiteral true, BinaryOperator.LogicalOr, oneEqualsSeventeen))
        compileCtl "Ctl.StateExpression(() => boolValue || 1 == intValue)" =? expected

    [<Test>]
    let ``transform enum literals in state expressions`` () =
        let expected = StateFormula (BinaryExpression (IntegerLiteral 1, BinaryOperator.Equals, IntegerLiteral 2))
        compileCtl "Ctl.StateExpression(() => enumValue == E.C)" =? expected

    [<Test>]
    let ``transform component indirect member access`` () =
        let actual = compileCtl "Ctl.StateExpression(() => accessIntField == intValue)"
        let fieldAccess = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[1], Some symbolResolver.ModelSymbol.ComponentObjects.[0])
        let expected = StateFormula (BinaryExpression (fieldAccess, BinaryOperator.Equals, IntegerLiteral 17))
        actual =? expected

    [<Test>]
    let ``transform component direct member access`` () =
        let actual = compileCtl "Ctl.StateExpression(() => !a.boolField)"
        let fieldAccess = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[0])
        let expected = StateFormula (UnaryExpression (fieldAccess, UnaryOperator.LogicalNot))
        actual =? expected

    [<Test>]
    let ``transform subcomponent direct member access`` () =
        let actual = compileCtl "Ctl.StateExpression(() => !sub.boolField)"
        let fieldAccess = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[2])
        let expected = StateFormula (UnaryExpression (fieldAccess, UnaryOperator.LogicalNot))
        actual =? expected

    [<Test>]
    let ``transform mixed component member access`` () =
        let actual = compileCtl "Ctl.StateExpression(() => a.boolField != b.boolField)"
        let fieldAccessA = ReadField (symbolResolver.ComponentSymbols.[0].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[0])
        let fieldAccessB = ReadField (symbolResolver.ComponentSymbols.[1].Fields.[0], Some symbolResolver.ModelSymbol.ComponentObjects.[1])
        let expected = StateFormula (BinaryExpression (fieldAccessA, BinaryOperator.NotEquals, fieldAccessB))
        actual =? expected

    [<Test>]
    let ``transform next`` () =
        let expression = BinaryExpression (IntegerLiteral 17, BinaryOperator.GreaterThan, IntegerLiteral 89)
        compileCtl "Ctl.AllPaths.Next(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.AllPathsNext)

        compileCtl "Ctl.AllPaths.Next(Ctl.AllPaths.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.AllPathsNext), UnaryFormulaOperator.AllPathsNext)

        compileCtl "Ctl.ExistsPath.Next(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.ExistsPathNext)

        compileCtl "Ctl.ExistsPath.Next(Ctl.AllPaths.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.AllPathsNext), UnaryFormulaOperator.ExistsPathNext)

    [<Test>]
    let ``transform finally`` () =
        let expression = BinaryExpression (IntegerLiteral 17, BinaryOperator.GreaterThan, IntegerLiteral 89)
        compileCtl "Ctl.AllPaths.Finally(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.AllPathsFinally)

        compileCtl "Ctl.AllPaths.Finally(Ctl.AllPaths.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.AllPathsNext), UnaryFormulaOperator.AllPathsFinally)

        compileCtl "Ctl.ExistsPath.Finally(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.ExistsPathFinally)

        compileCtl "Ctl.ExistsPath.Finally(Ctl.AllPaths.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.AllPathsNext), UnaryFormulaOperator.ExistsPathFinally)

    [<Test>]
    let ``transform globally`` () =
        let expression = BinaryExpression (IntegerLiteral 17, BinaryOperator.GreaterThan, IntegerLiteral 89)
        compileCtl "Ctl.AllPaths.Globally(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.AllPathsGlobally)

        compileCtl "Ctl.AllPaths.Globally(Ctl.AllPaths.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.AllPathsNext), UnaryFormulaOperator.AllPathsGlobally)

        compileCtl "Ctl.ExistsPath.Globally(() => intValue > 89)" =? UnaryFormula(StateFormula expression, UnaryFormulaOperator.ExistsPathGlobally)

        compileCtl "Ctl.ExistsPath.Globally(Ctl.AllPaths.Next(() => boolValue))" =? 
            UnaryFormula(UnaryFormula(StateFormula (BooleanLiteral true), UnaryFormulaOperator.AllPathsNext), UnaryFormulaOperator.ExistsPathGlobally)

    [<Test>]
    let ``transform until`` () =
        let stateFormula = StateFormula (BooleanLiteral true)
        let nextFormula = UnaryFormula (stateFormula, UnaryFormulaOperator.AllPathsNext)

        compileCtl "Ctl.AllPaths.Until(() => boolValue, () => boolValue)" =? 
            BinaryFormula(stateFormula, BinaryFormulaOperator.AllPathsUntil, stateFormula)

        compileCtl "Ctl.AllPaths.Until(Ctl.AllPaths.Next(() => boolValue), () => boolValue)" =? 
            BinaryFormula(nextFormula, BinaryFormulaOperator.AllPathsUntil, stateFormula)

        compileCtl "Ctl.AllPaths.Until(() => boolValue, Ctl.AllPaths.Next(() => boolValue))" =? 
            BinaryFormula(stateFormula, BinaryFormulaOperator.AllPathsUntil, nextFormula)

        compileCtl "Ctl.AllPaths.Until(Ctl.AllPaths.Next(() => boolValue), Ctl.AllPaths.Next(() => boolValue))" =? 
            BinaryFormula(nextFormula, BinaryFormulaOperator.AllPathsUntil, nextFormula)

        compileCtl "Ctl.ExistsPath.Until(() => boolValue, () => boolValue)" =? 
            BinaryFormula(stateFormula, BinaryFormulaOperator.ExistsPathUntil, stateFormula)

        compileCtl "Ctl.ExistsPath.Until(Ctl.AllPaths.Next(() => boolValue), () => boolValue)" =? 
            BinaryFormula(nextFormula, BinaryFormulaOperator.ExistsPathUntil, stateFormula)

        compileCtl "Ctl.ExistsPath.Until(() => boolValue, Ctl.AllPaths.Next(() => boolValue))" =? 
            BinaryFormula(stateFormula, BinaryFormulaOperator.ExistsPathUntil, nextFormula)

        compileCtl "Ctl.ExistsPath.Until(Ctl.AllPaths.Next(() => boolValue), Ctl.AllPaths.Next(() => boolValue))" =? 
            BinaryFormula(nextFormula, BinaryFormulaOperator.ExistsPathUntil, nextFormula)