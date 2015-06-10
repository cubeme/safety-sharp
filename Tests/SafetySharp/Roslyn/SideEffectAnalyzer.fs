// The MIT License (MIT)
// open SafetySharp.Modeling
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

namespace Roslyn

open System
open System.Linq
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Compiler.Roslyn
open SafetySharp.Compiler.Roslyn.Syntax

[<TestFixture>]
module SideEffectAnalyzer =

    let isSideEffectFree expression = 
        let compilation = TestCompilation ("
            struct S 
            {
                public static S operator+(S s) { return s; }
                public static S operator-(S s) { return s; }
                public static S operator!(S s) { return s; }
                public static S operator~(S s) { return s; }
                public static S operator+(S s1, S s2) { return s1; }
                public static S operator-(S s1, S s2) { return s1; }
                public static S operator*(S s1, S s2) { return s1; }
                public static S operator/(S s1, S s2) { return s1; }
                public static S operator%(S s1, S s2) { return s1; }
                public static bool operator==(S s1, S s2) { return false; }
                public static bool operator!=(S s1, S s2) { return false; }
                public static bool operator>=(S s1, S s2) { return false; }
                public static bool operator>(S s1, S s2) { return false; }
                public static bool operator<=(S s1, S s2) { return false; }
                public static bool operator<(S s1, S s2) { return false; }
                public static S operator&(S s1, S s2) { return s2; }
                public static S operator|(S s1, S s2) { return s1; }
                public static bool operator^(S s1, S s2) { return false; }
                public static S operator<<(S s, int x) { return s; }
                public static S operator>>(S s, int x) { return s; }
                public static bool operator true(S s) { return false; }
                public static bool operator false(S s) { return false; }
                public int this[int i] { get { return 1; } set { } }
                public static explicit operator int(S s) { return 1; }
                public static explicit operator S(int i) { return new S(); }
            }

            class Y 
            {
                public int _baseField;
                public int BaseProperty { get; set; }
                public Y Self { get; set; }
            }

            class X : Y
            { 
                int _field;
                bool Property { get; set; }
                void M() 
                { 
                    S s = new S();
                    int a = 0, b = 0;
                    bool c = false, d = false;
                    decimal e = 1, f = 3;
                    var array = new int[3];
                    var x = new X();
                    var result = " + expression + "; 
                }
            }
        ")

        let methodDeclaration = compilation.FindMethodDeclaration "X" "M"
        let lastStatement = methodDeclaration.Body.Statements.Last () :?> LocalDeclarationStatementSyntax

        let analyzer = SideEffectAnalyzer compilation.SemanticModel
        analyzer.IsSideEffectFree lastStatement.Declaration.Variables.[0].Initializer.Value

    [<Test>]
    let ``throws when semantic model is null`` () =
        raisesArgumentNullException "semanticModel" (fun () -> SideEffectAnalyzer null |> ignore)

    [<Test>]
    let ``throws when expression is null`` () =
        let compilation = TestCompilation ""
        let analyzer = SideEffectAnalyzer compilation.SemanticModel
        raisesArgumentNullException "expression" (fun () -> analyzer.IsSideEffectFree null |> ignore)

    [<Test>]
    let ``literals are side effect free`` () =
        isSideEffectFree "1" =? true
        isSideEffectFree "false" =? true
        isSideEffectFree "1.3m" =? true

    [<Test>]
    let ``reads of local variables are side effect free`` () =
        isSideEffectFree "a" =? true
        isSideEffectFree "c" =? true
        isSideEffectFree "e" =? true

    [<Test>]
    let ``reads of fields are side effect free`` () =
        isSideEffectFree "_field" =? true
        isSideEffectFree "x._field" =? true
        isSideEffectFree "this._field" =? true
        isSideEffectFree "_baseField" =? true
        isSideEffectFree "x._baseField" =? true
        isSideEffectFree "base._baseField" =? true
        isSideEffectFree "this._baseField" =? true

    [<Test>]
    let ``reads of properties are not side effect free`` () =
        isSideEffectFree "Property" =? false
        isSideEffectFree "x.Property" =? false
        isSideEffectFree "this.Property" =? false
        isSideEffectFree "BaseProperty" =? false
        isSideEffectFree "x.BaseProperty" =? false
        isSideEffectFree "this.BaseProperty" =? false
        isSideEffectFree "base.BaseProperty" =? false
        isSideEffectFree "base.Self._baseField" =? false

    [<Test>]
    let ``unary expressions on literals are side effect free`` () =
        isSideEffectFree "+1" =? true
        isSideEffectFree "-1.3m" =? true
        isSideEffectFree "~1" =? true
        isSideEffectFree "!true" =? true

    [<Test>]
    let ``non-increment/decrement unary expressions on local variables are side effect free`` () =
        isSideEffectFree "+b" =? true
        isSideEffectFree "-f" =? true
        isSideEffectFree "~a" =? true
        isSideEffectFree "!c" =? true

    [<Test>]
    let ``increment/decrement unary expressions on local variables are not side effect free`` () =
        isSideEffectFree "++b" =? false
        isSideEffectFree "++f" =? false
        isSideEffectFree "b++" =? false
        isSideEffectFree "f++" =? false
        isSideEffectFree "--b" =? false
        isSideEffectFree "--f" =? false
        isSideEffectFree "b--" =? false
        isSideEffectFree "f--" =? false

    [<Test>]
    let ``nested unary expressions check their operands`` () =
        isSideEffectFree "+(++b)" =? false
        isSideEffectFree "-(f--)" =? false

    [<Test>]
    let ``parenthesized expressions return whether their contained expression is side effect free`` () =
        isSideEffectFree "(1)" =? true
        isSideEffectFree "(++a)" =? false

    [<Test>]
    let ``non-increment/decrement unary expressions on local variables of user-defined type are not side effect free`` () =
        isSideEffectFree "+s" =? false
        isSideEffectFree "-s" =? false
        isSideEffectFree "~s" =? false
        isSideEffectFree "!s" =? false

    [<Test>]
    let ``binary expressions on literals are side effect free`` () =
        isSideEffectFree "1 + 1" =? true
        isSideEffectFree "2 - 1.3m" =? true
        isSideEffectFree "1 * 1" =? true
        isSideEffectFree "1 / 1" =? true
        isSideEffectFree "1 % 1" =? true
        isSideEffectFree "2 << 4" =? true
        isSideEffectFree "2 >> 1" =? true
        isSideEffectFree "true && false" =? true
        isSideEffectFree "true || false" =? true
        isSideEffectFree "true & false" =? true
        isSideEffectFree "true | false" =? true
        isSideEffectFree "true ^ false" =? true
        isSideEffectFree "1 == 1" =? true
        isSideEffectFree "1 != 1" =? true
        isSideEffectFree "1 >= 1" =? true
        isSideEffectFree "1 > 1" =? true
        isSideEffectFree "1 <= 1" =? true
        isSideEffectFree "1 < 1" =? true

    [<Test>]
    let ``binary expressions on local variables are side effect free`` () =
        isSideEffectFree "a + a" =? true
        isSideEffectFree "e - f" =? true
        isSideEffectFree "a * a" =? true
        isSideEffectFree "a / a" =? true
        isSideEffectFree "a % a" =? true
        isSideEffectFree "a << b" =? true
        isSideEffectFree "b >> a" =? true
        isSideEffectFree "c && d" =? true
        isSideEffectFree "c || d" =? true
        isSideEffectFree "c & d" =? true
        isSideEffectFree "c | d" =? true
        isSideEffectFree "c ^ d" =? true
        isSideEffectFree "a == a" =? true
        isSideEffectFree "a != a" =? true
        isSideEffectFree "a >= a" =? true
        isSideEffectFree "a > a" =? true
        isSideEffectFree "a <= a" =? true
        isSideEffectFree "a < a" =? true

    [<Test>]
    let ``nested binary expressions check their operands`` () =
        isSideEffectFree "1 + (++b)" =? false
        isSideEffectFree "a == ++a" =? false
        isSideEffectFree "c && (a++ == 1 || (++b == --a) == (c ^ (d == (--b > 1))))" =? false

    [<Test>]
    let ``binary expressions on local variables of user-defined type are not side effect free`` () =
        isSideEffectFree "s + s" =? false
        isSideEffectFree "s - s" =? false
        isSideEffectFree "s * s" =? false
        isSideEffectFree "s / s" =? false
        isSideEffectFree "s % s" =? false
        isSideEffectFree "s << b" =? false
        isSideEffectFree "s >> b" =? false
        isSideEffectFree "s && s" =? false
        isSideEffectFree "s || s" =? false
        isSideEffectFree "s & s" =? false
        isSideEffectFree "s | s" =? false
        isSideEffectFree "s ^ s" =? false
        isSideEffectFree "s == s" =? false
        isSideEffectFree "s != s" =? false
        isSideEffectFree "s >= s" =? false
        isSideEffectFree "s > s" =? false
        isSideEffectFree "s <= s" =? false
        isSideEffectFree "s < s" =? false

    [<Test>]
    let ``invocation expressions are always considered to have side effects`` () =
        isSideEffectFree "ToString()" =? false
        isSideEffectFree "GetHashCode()" =? false

    [<Test>]
    let ``object creation expressions are always considered to have side effects`` () =
        isSideEffectFree "new S()" =? false
        isSideEffectFree "new object()" =? false

    [<Test>]
    let ``array read accesses are always considered to be side effect free`` () =
        isSideEffectFree "array[0]" =? true

    [<Test>]
    let ``indexer read accesses are always considered to be side effect free`` () =
        isSideEffectFree "s[0]" =? false

    [<Test>]
    let ``assignments are archetypical side effects`` () =
        isSideEffectFree "a = 3" =? false
        isSideEffectFree "a = b = 12" =? false
        isSideEffectFree "c = false" =? false
        isSideEffectFree "array[1] = 3" =? false
        isSideEffectFree "s[1] = 3" =? false
        isSideEffectFree "_field = 1" =? false
        isSideEffectFree "x._field = 2" =? false
        isSideEffectFree "this._field = 3" =? false
        isSideEffectFree "_baseField = 2" =? false
        isSideEffectFree "x._baseField = 3" =? false
        isSideEffectFree "this._baseField = 1" =? false
        isSideEffectFree "base._baseField = 2" =? false
        isSideEffectFree "Property = true" =? false
        isSideEffectFree "x.Property = true" =? false
        isSideEffectFree "this.Property = true" =? false
        isSideEffectFree "BaseProperty = 2" =? false
        isSideEffectFree "x.BaseProperty = 3" =? false
        isSideEffectFree "this.BaseProperty = 3" =? false
        isSideEffectFree "base.BaseProperty = 4" =? false

    [<Test>]
    let ``built-in conversions are side effect free`` () =
        isSideEffectFree "(int)e" =? true
        isSideEffectFree "(decimal)a" =? true

    [<Test>]
    let ``built-in casts are side effect free`` () =
        isSideEffectFree "(Y)x" =? true
        isSideEffectFree "(X)((Y)x)" =? true

    [<Test>]
    let ``user-defined conversions are considered to have side effects`` () =
        isSideEffectFree "(int)s" =? false
        isSideEffectFree "(S)a" =? false
