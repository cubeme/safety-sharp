// The MIT License (MIT)
// open SafetySharp.Modeling
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

namespace Roslyn

open System
open System.Linq
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Tests
open SafetySharp.Modeling.CompilerServices
open SafetySharp.CSharpCompiler.Roslyn
open SafetySharp.CSharpCompiler.Roslyn.Syntax

[<TestFixture>]
module SideEffectAnalyzer =

    let isSideEffectFree expression = 
        let compilation = TestCompilation (sprintf "
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
                public static S operator%%(S s1, S s2) { return s1; }
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
            }

            class X 
            { 
                int _field;
                bool Property { get; set; }
                void M() 
                { 
                    S s = new S();
                    int a = 0, b = 0;
                    bool c = false, d = false;
                    decimal e = 1, f = 3;
                    var result = %s; 
                }
            }
        " expression)

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