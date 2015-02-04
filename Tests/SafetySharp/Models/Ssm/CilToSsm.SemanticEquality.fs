// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace Models.Ssm

open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<AutoOpen>]
module TestHelpers =
    let compile baseClass csharpCode additionalMembers fields replaceReturns = 
        let model = TestCompilation.CreateModel (sprintf "class TestModel : Model { public TestModel() { SetRootComponents(new O()); }} class O : Component { public %s %s %s }" csharpCode additionalMembers fields)
        model.FinalizeMetadata ()
        let root = CilToSsm.transformModel model
        let transformedMethod = root.Subs.[0].Methods |> Seq.find (fun m -> m.Name = CilToSsm.makeUniqueMethodName "M" 2 0) |> SsmToCSharp.transform

        // We remove all return statements from the method, as we assume that they are irrelevant (the code is transformed in such a way
        // that a conditional return results in subsequent code not being executed, regardless of whether the returning branch is taken).
        // By removing all returns, we test whether this assumption actually holds.
        // Note that this only works when the tests are void-returning...
        let transformedMethod = if replaceReturns then transformedMethod.Replace ("return;", ";") else transformedMethod
        let csharpCode = sprintf "class T : Models.Ssm.TestHelpers.%s { public override %s %s } class O : Models.Ssm.TestHelpers.%s { public override %s %s }" baseClass csharpCode additionalMembers baseClass transformedMethod additionalMembers
        let compilation = TestCompilation csharpCode
        compilation.Compile () |> ignore
        (compilation.CreateObject<'a> "T", compilation.CreateObject<'a> "O")

    [<AbstractClass>]
    type OneRefParam<'p, 'r when 'p : equality and 'r : equality> () =
        inherit Component ()
        static member Test (original : OneRefParam<'p, 'r>, transformed : OneRefParam<'p, 'r>) p =
            let originalParam = ref p
            let originalResult = original.M originalParam
            let transformedParam = ref p
            let transformedResult = transformed.M transformedParam

            originalParam =? transformedParam
            originalResult =? transformedResult
            original._f =? transformed._f

        abstract member M : 'p byref -> 'r
        [<DefaultValue>] val mutable _f : int

    [<AbstractClass>]
    type TwoRefParams<'p1, 'p2, 'r when 'p1 : equality and 'p2 : equality and 'r : equality> () =
        inherit Component ()
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
            original._f1 =? transformed._f1
            original._f2 =? transformed._f2

        abstract member M : 'p1 byref * 'p2 byref -> 'r
        [<DefaultValue>] val mutable _f1 : int
        [<DefaultValue>] val mutable _f2 : int

    [<AbstractClass>]
    type OneValParam<'p, 'r when 'p : equality and 'r : equality> () =
        inherit Component ()
        static member Test (original : OneValParam<'p, 'r>, transformed : OneValParam<'p, 'r>) p =
            let originalResult = original.M p
            let transformedResult = transformed.M p

            originalResult =? transformedResult
            original._f =? transformed._f

        abstract member M : 'p -> 'r
        [<DefaultValue>] val mutable _f : int

    [<AbstractClass>]
    type TwoValParams<'p1, 'p2, 'r when 'p1 : equality and 'p2 : equality and 'r : equality> () =
        inherit Component ()
        static member Test (original : TwoValParams<'p1, 'p2, 'r>, transformed : TwoValParams<'p1, 'p2, 'r>) p1 p2 =
            let originalResult = original.M p1 p2
            let transformedResult = transformed.M p1 p2

            originalResult =? transformedResult
            original._f1 =? transformed._f1
            original._f2 =? transformed._f2

        abstract member M : 'p1 -> 'p2 -> 'r
        [<DefaultValue>] val mutable _f1 : int
        [<DefaultValue>] val mutable _f2 : int

    [<AbstractClass>]
    type TwoValParamsVoid<'p1, 'p2 when 'p1 : equality and 'p2 : equality> () =
        inherit Component ()
        static member Test (original : TwoValParamsVoid<'p1, 'p2>, transformed : TwoValParamsVoid<'p1, 'p2>) p1 p2 =
            original.M p1 p2
            transformed.M p1 p2

            original._f1 =? transformed._f1
            original._f2 =? transformed._f2

        abstract member M : 'p1 -> 'p2 -> unit
        [<DefaultValue>] val mutable _f1 : int
        [<DefaultValue>] val mutable _f2 : int

    [<AbstractClass>]
    type FourValParams<'p1, 'p2, 'p3, 'p4, 'r when 'p1 : equality and 'p2 : equality and 'p3 : equality and 'p4 : equality and 'r : equality> () =
        inherit Component ()
        static member Test (original : FourValParams<'p1, 'p2, 'p3, 'p4, 'r>, transformed : FourValParams<'p1, 'p2, 'p3, 'p4, 'r>) p1 p2 p3 p4 =
            let originalResult = original.M p1 p2 p3 p4
            let transformedResult = transformed.M p1 p2 p3 p4

            originalResult =? transformedResult

        abstract member M : 'p1 -> 'p2 -> 'p3 -> 'p4 -> 'r

[<TestFixture>]
module ``CilToSsm Semantic Equality`` =

    let readField = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { return _f + x; }" "" "int _f;" false)
    let writeField = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { _f = x; return _f; }" "" "int _f;" false)
    let callMethodWithoutParameters = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { F(); return _f + x; }" "void F() { _f = 3; }" "int _f;" false)
    let callMethodWithParameter = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { _f = x + 2; return F(x); }" "int F(int x) { return x + _f; }" "int _f;" false)
    let callMethodHandleFieldAssignment = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { _f += _f > 0 ? F(2) : F(1); return _f; }" "int F(int x) { return x + (_f += 1); }" "int _f;" false)
    let readFieldWithRefParam = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int x) { x = _f; return x; }" "" "int _f;" false)
    let writeFieldWithRefParam = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int x) { _f = x; return _f; }" "" "int _f;" false)
    let fieldAccessWithSideEffects1 = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { x += _f + ((x = _f = ++_f) > 0 ? ++_f : ((_f += _f) + _f)); return x; }" "" "int _f;" false)
    let fieldAccessWithSideEffects2 = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { return x *=  _f + (x * 2 - ((_f = --_f) > 0 ? ++_f : (_f += _f)) + _f); }" "" "int _f;" false)    
    let readFromRef = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int x) { return x; }" "" "" false)
    let writeToRef = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int x) { x = 17; return x; }" "" "" false)
    let complexSideEffects = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int z) { z *= z-- * --z; return z; }" "" "" false)
    let complexSideEffectsRef = OneRefParam<int, int>.Test (compile "OneRefParam<int, int>" "int M(ref int z) { z *= z-- * --z; return z; }" "" "" false)
    let refParamsComplexControlFlow = TwoRefParams<bool, int, int>.Test (compile "TwoRefParams<bool, int, int>" "int M(ref bool y, ref int z) { z = y ? z++ : ((y = !y) ? z-- : --z); return z; }" "" "" false)
    let ternaryOperatorBeforeReturn = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { var y = x > 0 ? -1 : 1; return y - 1; }" "" "" false)
    let ternaryOperatorBeforeReturnOnField = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { var y = x + _f > 0 ? -1 : 1; return y - 1 - _f; }" "" "int _f;" false)
    let ternaryOperatorWithSideEffect1 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { return x > 0 ? ++y : 0; }" "" "" false)
    let ternaryOperatorWithSideEffect2 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { return x > 0 ? y-- : 0; }" "" "" false)
    let nestedTernaryOperator = TwoValParams<bool, bool, int>.Test (compile "TwoValParams<bool, bool, int>" "int M(bool b, bool c) { var x = 1 + (b ? (c ? 4 : 2) : 3); return x; }" "" "" false)
    let complexControlFlowAndSideEffects = TwoValParams<bool, int, int>.Test (compile "TwoValParams<bool, int, int>" "int M(bool b, int c) { var x = 1 + ((b = !b) ? (c++ > 2 ? c-- : --c) : ((b = (!b ? (b = !b) : b)) ? c += 17 : c -= 8)); return x; }" "" "" false)
    let complexControlFlowAndSideEffectsRef = TwoRefParams<bool, int, int>.Test (compile "TwoRefParams<bool, int, int>" "int M(ref bool b, ref int c) { var x = 1 + ((b = !b) ? (c++ > 2 ? c-- : --c) : ((b = (!b ? (b = !b) : b)) ? c += 17 : c -= 8)); return x; }" " """ false)
    let sideEffectsRef = OneRefParam<bool, int>.Test (compile "OneRefParam<bool, int>" "int M(ref bool b) { return 1 + ((b = (!b ? (b = !b) : b)) ? 17 : 8); }" "" "" false)
    let shortCircuitOrBool = TwoValParams<bool, bool, int>.Test (compile "TwoValParams<bool, bool, int>" "int M(bool x, bool y) { if (x || y) return -1; return 0; }" "" "" false)
    let shortCircuitWithField = TwoValParams<bool, int, int>.Test (compile "TwoValParams<bool, int, int>" "int M(bool x, int y) { _f1 = y; if (x || _f1 < 1) return -1; return 0; }" "" "int _f1;" false)
    let shortCircuitAndBool = TwoValParams<bool, bool, int>.Test (compile "TwoValParams<bool, bool, int>" "int M(bool x, bool y) { if (x && y) return -1; return 0; }" "" "" false)
    let controlFlowAndSideEffects1 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { var r = x + y / 2; if ((r *= 2) == y++ || y-- == --y) r += y * x; else r--; return r; }" "" "" false)
    let controlFlowAndSideEffects2 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { if ((x += x) > y || --y == 0) x++; else if (x - 2 < y + 1 || --y == 0) { --y; if (++x == --y) --y; } else x -= 1; return x *= y * 2; }" "" "" false)
    let controlFlowAndSideEffects3 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { if ((x + x) > y || y == 0) x++; else if (x - 2 < y + 1 || y - 1 == 0) { --y; if (x == y) --y; } else x -= 1; return x *= y * 2; }" "" "" false)
    let controlFlowAndSideEffects4 = FourValParams<int, bool, bool, bool, int>.Test (compile "FourValParams<int, bool, bool, bool, int>" "int M(int arg1, bool arg2, bool arg3, bool arg4) { var loc0 = 0; if (arg1 > 0) loc0 += arg1; var loc1 = loc0 != 0; var loc2 = !arg2 && arg3; var loc3 = arg4 && !loc2 && loc1; var loc4 = arg4 && loc2 && loc1; if (loc3) --loc0; if (loc4) --loc0; return loc0; }" "" "" false)
    let controlFlowAndSideEffects5 = FourValParams<int, bool, bool, bool, int>.Test (compile "FourValParams<int, bool, bool, bool, int>" "int M(int arg1, bool arg2, bool arg3, bool arg4) { var loc0 = 0; if (arg1 > 0) loc0 += arg1; var loc1 = loc0 != 0; var loc2 = !arg2 & arg3; var loc3 = arg4 & !loc2 & loc1; var loc4 = arg4 & loc2 & loc1; if (loc3) --loc0; if (loc4) --loc0; return loc0; }" "" "" false)
    let controlFlowAndSideEffects6 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { if ((x += _f1 = x) > y || --y == 0) x++; else if (x + (_f1++) - 2 < y + 1 || --y == 0) { --y; if ((_f2 = ++x) == --y - --_f2) --y; } else x -= 1; return x *=  _f1 + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2)) + _f2); }" "" "int _f1; int _f2;" false)
    let controlFlowAndSideEffects7 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { return _f1 += F1(_f2--); }" "int F1(int x) { ++_f1; _f2 += x; return x; } int F2() { return ++_f1; } void F3() { --_f2; }" "int _f1; int _f2;" false)
    let controlFlowAndSideEffects8 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { F3(); if ((x += _f1 = x) > y || --y == 0) { F3(); x++; } else if (x + (_f1++) - 2 < y + 1 || --y == 0) { --y; if ((_f2 = ++x) == --y - (_f2 = (--_f2 + F1(_f2)))) --y; } else x -= 1; return x *=  _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2); }" "int F1(int x) { ++_f1; _f2 += x; return x; } int F2() { return ++_f1; } void F3() { --_f2; }" "int _f1; int _f2;" false)
    let valParamByRef = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { F(ref x, out y); return x + y; }" "void F(ref int x, out int y) { x = x + 1; y = x; }" "" false)
    let refParamByRef = TwoRefParams<int, int, int>.Test (compile "TwoRefParams<int, int, int>" "int M(ref int x, ref int y) { F(ref x, out y); return x + y; }" "void F(ref int x, out int y) { x = x + 1; y = x; }" "" false)
    let localByRef = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { int y = x; int z = x + 1; F(ref y, out z); return z + x + y; }" "void F(ref int x, out int y) { x = x + 1; y = x; }" "" false)
    let fieldByRef = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { _f = x; F(ref _f, out _f); return _f; }" "void F(ref int x, out int y) { x = x + 1; y = x; }" "int _f;" false)
    let complexControlFlowAndRefArgs1 = TwoValParams<int, int, int>.Test (compile "TwoValParams<int, int, int>" "int M(int x, int y) { _f1 = x; if (x > 0 || F(ref x, out y) && !F(ref _f1, out _f2)) { F(ref y, out _f1); } return x + _f1 + _f2 + y + (_f1 > 0 && F(ref x, out x) ? (F(ref _f2, out y) ? 1 : 0) : F(ref x, out x) ? 0 : 1) + x + _f1 + _f2 + y; }" "bool F(ref int x, out int y) { x = x + 1; y = x; return y > 0; }" "int _f1; int _f2;" false)
    let complexControlFlowAndRefArgs2 = TwoRefParams<int, int, int>.Test (compile "TwoRefParams<int, int, int>" "int M(ref int x, ref int y) { _f1 = x; if (x > 0 || F(ref x, out y) && !F(ref _f1, out _f2)) { F(ref y, out _f1); } return x + _f1 + _f2 + y + (_f1 > 0 && F(ref x, out x) ? (F(ref _f2, out y) ? 1 : 0) : F(ref x, out x) ? 0 : 1) + x + _f1 + _f2 + y; }" "bool F(ref int x, out int y) { x = x + 1; y = x; return y > 0; }" "int _f1; int _f2;" false)
    let callStaticAndNonThisMethods = OneValParam<int, int>.Test (compile "OneValParam<int, int>" "int M(int x) { return x + x > 0 ? q.M(ref x) + Q.S(ref x) : Q.S(ref x) - q.M(ref x); }" "Q q = new Q(); class Q { public int M(ref int x) { return x++; } public static int S (ref int x) { return x--; }}" "" false)
    let simpleReturningMethod = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { if (x == y) return; _f1 = x; return; _f2 = y; }" "" "int _f1; int _f2;" true)
    let returningControlFlowAndSideEffects1 = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { if ((x += _f1 = x) > y || --y == 0) x++; else if (x + (_f1++) - 2 < y + 1 || --y == 0) { --y; if ((_f2 = ++x) == --y - --_f2) --y; return; } else x -= 1; _f1 = x * _f1 + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2)) + _f2); }" "" "int _f1; int _f2;" true)
    let returningControlFlowAndSideEffects2 = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { if ((x += _f1 = x) > y || --y == 0) { x++; return; } else if (x + (_f1++) - 2 < y + 1 || --y == 0) { --y; if ((_f2 = ++x) == --y - --_f2) --y; } else x -= 1; _f1 = x * _f1 + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2)) + _f2); }" "" "int _f1; int _f2;" true)
    let returningControlFlowAndSideEffects3 = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { if ((_f1 += F1(_f2--)) == 2) return; _f2 = F2() + F3(); }" "int F1(int x) { ++_f1; _f2 += x; return x; } int F2() { return ++_f1; } int F3() { return --_f2; }" "int _f1; int _f2;" true)
    let returningControlFlowAndSideEffects4 = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { F3(); if ((x += _f1 = x) > y || --y == 0) { F3(); x++; return; } else if (x + (_f1++) - 2 < y + 1 || --y == 0) { _f1 = --y; if ((_f2 = ++x) == --y - (_f2 = (--_f2 + F1(_f2)))) --y; } else x -= 1; _f1 = _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2); }" "int F1(int x) { ++_f1; _f2 += x; return x; } int F2() { return ++_f1; } void F3() { --_f2; }" "int _f1; int _f2;" true)
    let returningControlFlowAndSideEffects5 = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { F3(); if ((x += _f1 = x) > y || --y == 0) { F3(); x++; } else if (x + (_f1++) - 2 < y + 1 || --y == 0) { --y; if ((_f2 = ++x) == --y - (_f2 = (--_f2 + F1(_f2)))) { _f2 = --y; return; } } else x -= 1; _f1 = _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2); }" "int F1(int x) { ++_f1; _f2 += x; return x; } int F2() { return ++_f1; } void F3() { --_f2; }" "int _f1; int _f2;" true)
    let returningControlFlowAndSideEffects6 = TwoValParamsVoid<int, int>.Test (compile "TwoValParamsVoid<int, int>" "void M(int x, int y) { F3(); if ((x += _f1 = x) > y || --y == 0) { F3(); x++; } else if (x + (_f1++) - 2 < y + 1 || --y == 0) { --y; if ((_f2 = ++x) == --y - (_f2 = (--_f2 + F1(_f2)))) --y; } else { _f2 = x -= 1; return; } _f1 = _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2); }" "int F1(int x) { ++_f1; _f2 += x; return x; } int F2() { return ++_f1; } void F3() { --_f2; }" "int _f1; int _f2;" true)

    [<Test>]
    let ``read field`` ([<Range (-1, 1)>] p) =
        readField p

    [<Test>]
    let ``write field`` ([<Range (-1, 1)>] p) =
        writeField p

    [<Test>]
    let ``call method without parameters`` ([<Range (0, 1)>] p) =
        callMethodWithParameter p

    [<Test>]
    let ``call method with parameter`` ([<Range (-1, 1)>] p) =
        callMethodWithParameter p

    [<Test>]
    let ``call method and handle field assignment during method`` ([<Range (-1, 1)>] p) =
        callMethodHandleFieldAssignment p

    [<Test>]
    let ``read field with ref param`` ([<Range (-1, 1)>] p) =
        readFieldWithRefParam p

    [<Test>]
    let ``write field with ref param`` ([<Range (-1, 1)>] p) =
        writeFieldWithRefParam p

    [<Test>]
    let ``field access with side effects 1`` ([<Range (-3, 3)>] p) =
        fieldAccessWithSideEffects1 p

    [<Test>]
    let ``field access with side effects 2`` ([<Range (-3, 3)>] p) =
        fieldAccessWithSideEffects2 p

    [<Test>]
    let ``read from ref parameter`` ([<Range (-1, 1)>] p) =
        readFromRef p

    [<Test>]
    let ``write to ref parameter`` ([<Range (-1, 1)>] p) =
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
    let ``ternary operator before return with field access`` ([<Range (-5, 5)>] p) =
        ternaryOperatorBeforeReturnOnField p

    [<Test>]
    let ``short-circuit 'or' for Boolean variables and return`` ([<Values (true, false)>] p1) ([<Values (true, false)>] p2) = 
        shortCircuitOrBool p1 p2

    [<Test>]
    let ``short-circuit 'and' for Boolean variables and return`` ([<Values (true, false)>] p1) ([<Values (true, false)>] p2) = 
        shortCircuitAndBool p1 p2

    [<Test>]
    let ``short-circuit with field access`` ([<Values (true, false)>] p1) ([<Range (-5, 5)>] p2) = 
        shortCircuitWithField p1 p2

    [<Test>]
    let ``tenary operator with preincrement side effect`` ([<Range (-5, 5)>] p1) ([<Range (-5, 5)>] p2) =
        ternaryOperatorWithSideEffect1 p1 p2

    [<Test>]
    let ``tenary operator with postdecrement side effect`` ([<Range (-5, 5)>] p1) ([<Range (-5, 5)>] p2) =
        ternaryOperatorWithSideEffect2 p1 p2

    [<Test>]
    let ``nested ternary operator`` ([<Values (true, false)>] p1) ([<Values (true, false)>] p2) =
        nestedTernaryOperator p1 p2

    [<Test>]
    let ``side effects on ref parameters`` ([<Values (true, false)>] p) =
        sideEffectsRef p

    [<Test>]
    let ``complex control flow and side effects`` ([<Values (true, false)>] p1) ([<Range (-5, 5)>] p2) =
        complexControlFlowAndSideEffects p1 p2

    [<Test>]
    let ``complex control flow and side effects with ref params`` ([<Values (true, false)>] p1) ([<Range (-5, 5)>] p2) =
        complexControlFlowAndSideEffectsRef p1 p2

    [<Test>]
    let ``control flow and side effects 1`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        controlFlowAndSideEffects1 p1 p2

    [<Test>]
    let ``control flow and side effects 2`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        controlFlowAndSideEffects2 p1 p2

    [<Test>]
    let ``control flow and side effects 3`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        controlFlowAndSideEffects3 p1 p2

    [<Test>]
    let ``control flow and side effects 4`` ([<Range (-5, 5)>] p1) ([<Values (true, false)>] p2) ([<Values (true, false)>] p3) ([<Values (true, false)>] p4) =
        controlFlowAndSideEffects4 p1 p2 p3 p4

    [<Test>]
    let ``control flow and side effects 5`` ([<Range (-5, 5)>] p1) ([<Values (true, false)>] p2) ([<Values (true, false)>] p3) ([<Values (true, false)>] p4) =
        controlFlowAndSideEffects5 p1 p2 p3 p4

    [<Test>]
    let ``control flow and side effects 6`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        controlFlowAndSideEffects6 p1 p2

    [<Test>]
    let ``control flow and side effects 7`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        controlFlowAndSideEffects7 p1 p2

    [<Test>]
    let ``control flow and side effects 8`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        controlFlowAndSideEffects8 p1 p2

    [<Test>]
    let ``value parameters are passed as ref and out parameters to function`` ([<Range (-2, 2)>] p1) ([<Range (-2, 2)>] p2) =
        valParamByRef p1 p2

    [<Test>]
    let ``byref parameters are passed as ref and out parameters to function`` ([<Range (-2, 2)>] p1) ([<Range (-2, 2)>] p2) =
        refParamByRef p1 p2

    [<Test>]
    let ``locals are passed as ref and out parameters to function`` ([<Range (-2, 2)>] p) =
        localByRef p

    [<Test>]
    let ``field is passed as ref and out parameters to function`` ([<Range (-2, 2)>] p) =
        fieldByRef p

    [<Test>]
    let ``complex control flow and arguments passed byref with value arguments`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        complexControlFlowAndRefArgs1 p1 p2

    [<Test>]
    let ``complex control flow and arguments passed byref with byref arguments`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        complexControlFlowAndRefArgs2 p1 p2

    [<Test>]
    let ``call static and non-this methods`` ([<Range (-3, 3)>] p) =
        callStaticAndNonThisMethods p

    [<Test>]
    let ``simple returning Method`` ([<Range (-3, 3)>] p1) ([<Range (-3, 3)>] p2) =
        simpleReturningMethod p1 p2

    [<Test>]
    let ``returning control flow and side effects 1`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        returningControlFlowAndSideEffects1 p1 p2

    [<Test>]
    let ``returning control flow and side effects 2`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        returningControlFlowAndSideEffects2 p1 p2

    [<Test>]
    let ``returning control flow and side effects 3`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        returningControlFlowAndSideEffects3 p1 p2

    [<Test>]
    let ``returning control flow and side effects 4`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        returningControlFlowAndSideEffects4 p1 p2

    [<Test>]
    let ``returning control flow and side effects 5`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        returningControlFlowAndSideEffects5 p1 p2

    [<Test>]
    let ``returning control flow and side effects 6`` ([<Range (-10, 10)>] p1) ([<Range (-10, 10)>] p2) =
        returningControlFlowAndSideEffects6 p1 p2