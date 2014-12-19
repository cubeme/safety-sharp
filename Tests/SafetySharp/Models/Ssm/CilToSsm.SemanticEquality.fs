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

namespace Ssm

open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<AutoOpen>]
module TestHelpers =
    let compile baseClass csharpCode = 
        let csharpCode = sprintf "class O : Ssm.TestHelpers.%s { public override %s }" baseClass csharpCode
        let compilation = TestCompilation csharpCode
        let assembly = compilation.GetAssemblyDefinition ()
        let typeDef = assembly.MainModule.GetType "O"
        let methodDef = typeDef.Methods.Single (fun m' -> m'.Name = "M")
        let transformedMethod = methodDef |> CilToSsm.transformMethod |> SsmToCSharp.transform

        let csharpCode = sprintf "%s class T : Ssm.TestHelpers.%s { public override %s }" csharpCode baseClass transformedMethod
        let compilation = TestCompilation csharpCode
        compilation.Compile () |> ignore
        (compilation.CreateObject<'a> "O", compilation.CreateObject<'a> "T")

    [<AbstractClass>]
    type OneRefParam<'p, 'r when 'p : equality and 'r : equality> () =
        static member Test (original : OneRefParam<'p, 'r>, transformed : OneRefParam<'p, 'r>) p =
            let originalParam = ref p
            let originalResult = original.M originalParam
            let transformedParam = ref p
            let transformedResult = transformed.M transformedParam

            originalParam =? transformedParam
            originalResult =? transformedResult

        abstract member M : 'p byref -> 'r

    [<AbstractClass>]
    type TwoRefParams<'p1, 'p2, 'r when 'p1 : equality and 'p2 : equality and 'r : equality> () =
        static member Test (original : TwoRefParams<'p1, 'p2, 'r>, transformed : TwoRefParams<'p1, 'p2, 'r>) p1 p2 =
            let originalParam1 = ref p1
            let originalParam2 = ref p2
            let originalResult = original.M (originalParam1, originalParam2)
            let transformedParam1 = ref p1
            let transformedParam2 = ref p2
            let transformedResult = transformed.M (transformedParam1, transformedParam2)

            originalParam1 =? transformedParam1
            originalParam2 =? transformedParam2
            originalResult =? transformedResult

        abstract member M : 'p1 byref * 'p2 byref -> 'r

    [<AbstractClass>]
    type OneValParam<'p, 'r when 'p : equality and 'r : equality> () =
        static member Test (original : OneValParam<'p, 'r>, transformed : OneValParam<'p, 'r>) p =
            let originalResult = original.M p
            let transformedResult = transformed.M p

            originalResult =? transformedResult

        abstract member M : 'p -> 'r

    [<AbstractClass>]
    type TwoValParams<'p1, 'p2, 'r when 'p1 : equality and 'p2 : equality and 'r : equality> () =
        static member Test (original : TwoValParams<'p1, 'p2, 'r>, transformed : TwoValParams<'p1, 'p2, 'r>) p1 p2 =
            let originalResult = original.M p1 p2
            let transformedResult = transformed.M p1 p2

            originalResult =? transformedResult

        abstract member M : 'p1 -> 'p2 -> 'r

[<TestFixture>]
module ``CilToSsm Method Semantic Equality`` =

    let readFromRef = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int x) { return x; }")
    let writeToRef = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int x) { x = 17; return x; }")
    let complexSideEffects = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int z) { z *= z-- * --z; return z; }")
    let complexSideEffectsRef = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int z) { z *= z-- * --z; return z; }")
    let refParamsComplexControlFlow = TwoRefParams<bool, int, int>.Test (compile "TwoRefParams<bool, int, int>" "int M(ref bool y, ref int z) { z = y ? z++ : ((y = !y) ? z-- : --z); return z; }")
    let ternaryOperatorBeforeReturn = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { var y = x > 0 ? -1 : 1; return y - 1; }")
    let ternaryOperatorWithSideEffect1 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { return x > 0 ? ++y : 0; }")
    let ternaryOperatorWithSideEffect2 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { return x > 0 ? y-- : 0; }")
    let nestedTernaryOperator = TwoValParams<bool, bool, int>.Test (compile "TwoValParams<bool, bool, int>" "int M(bool b, bool c) { var x = 1 + (b ? (c ? 4 : 2) : 3); return x; }")
    let shortCircuitOrBool = TwoValParams<bool, bool, int>.Test (compile "TwoValParams<bool, bool, int>" "int M(bool x, bool y) { if (x || y) return -1; return 0; }")
    let shortCircuitAndBool = TwoValParams<bool, bool, int>.Test (compile "TwoValParams<bool, bool, int>" "int M(bool x, bool y) { if (x && y) return -1; return 0; }")

    [<Test>]
    let ``read from ref parameter`` ([<Range (-5, 5)>] p) =
        readFromRef p

    [<Test>]
    let ``write to ref parameter`` ([<Range (-5, 5)>] p) =
        writeToRef p

    [<Test>]
    let ``method with complex side effects`` ([<Range (-5, 5)>] p) =
        complexSideEffects p

    [<Test>]
    let ``method with complex side effects when parameter is byref`` ([<Range (-5, 5)>] p) =
        complexSideEffectsRef p

    [<Test>]
    let ``method with in and inout parameters, side effects, and complex control flow`` ([<Values (true, false)>] p1) ([<Range (-20, 20)>] p2) =
        refParamsComplexControlFlow p1 p2

    [<Test>]
    let ``ternary operator before return`` ([<Range (-5, 5)>] p) =
        ternaryOperatorBeforeReturn p

    [<Test>]
    let ``short-circuit 'or' for Boolean variables and return`` ([<Values (true, false)>] p1) ([<Values (true, false)>] p2) = 
        shortCircuitOrBool p1 p2

    [<Test>]
    let ``short-circuit 'and' for Boolean variables and return`` ([<Values (true, false)>] p1) ([<Values (true, false)>] p2) = 
        shortCircuitAndBool p1 p2

    [<Test>]
    let ``tenary operator with preincrement side effect`` ([<Range (-5, 5)>] p1) ([<Range (-5, 5)>] p2) =
        ternaryOperatorWithSideEffect1 p1 p2

    [<Test>]
    let ``tenary operator with postdecrement side effect`` ([<Range (-5, 5)>] p1) ([<Range (-5, 5)>] p2) =
        ternaryOperatorWithSideEffect2 p1 p2

    [<Test>]
    let ``nested ternary operator`` ([<Values (true, false)>] p1) ([<Values (true, false)>] p2) =
        nestedTernaryOperator p1 p2