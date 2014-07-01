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

namespace SafetySharp.Tests.CSharp.Roslyn.SyntaxTests

open System
open System.Linq
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.Internal.CSharp.Roslyn

[<AutoOpen>]
module SyntaxTestsHelpers =
    let toString (node : SyntaxNode) =
        node.ToFullString().Replace ("\r", String.Empty)

[<TestFixture>]
module ``AsSingleLine method`` =
    
    let asSingleLine csharpCode =
        SyntaxFactory.ParseStatement csharpCode |> Syntax.AsSingleLine |> toString

    [<Test>]
    let ``throws when null is passed`` () =
        raisesArgumentNullException "syntaxNode" <@ Syntax.AsSingleLine null @>

    [<Test>]
    let ``does not modify single line statements`` () =
        asSingleLine "var x = 1;" =? "var x = 1;"
        asSingleLine "if (true) ; else return;" =? "if (true) ; else return;"

    [<Test>]
    let ``modifies multi-line statements`` () =
        asSingleLine "var\nx =\n1;" =? "var x = 1;"
        asSingleLine "if\n(true)\n; else\nreturn;" =? "if (true) ; else return;"

[<TestFixture>]
module ``EnsureSameLineCount method`` =

    let ensureSameLineCount csharpCode templateCSharpCode =
        let templateNode = SyntaxFactory.ParseStatement templateCSharpCode
        SyntaxFactory.ParseStatement csharpCode |> Syntax.EnsureSameLineCount templateNode |> toString

    [<Test>]
    let ``throws when syntax node is null`` () =
        raisesArgumentNullException "syntaxNode" <@ Syntax.EnsureSameLineCount (SyntaxFactory.ParseExpression "1") null @>

    [<Test>]
    let ``throws when template node is null`` () =
        raisesArgumentNullException "templateNode" <@ Syntax.EnsureSameLineCount null (SyntaxFactory.ParseExpression "1") @>

    [<Test>]
    let ``throws when syntax node has more lines than template node`` () =
        let syntaxNode = SyntaxFactory.ParseExpression "1 +\n 1"
        let templateNode = SyntaxFactory.ParseExpression "1 + 1"
        raises<InvalidOperationException> <@ Syntax.EnsureSameLineCount templateNode syntaxNode @>

    [<Test>]
    let ``does not modify syntax node when line counts match`` () =
        ensureSameLineCount "var x = 1;" "    var x =   1;" =? "var x = 1;"
        ensureSameLineCount "if (true) ; else return;" "var y = 1 + 1" =? "if (true) ; else return;"

    [<Test>]
    let ``adds trailing new lines when syntax node has less lines than template node`` () =
        ensureSameLineCount "var x = 1;" " var x \n=   1;" =? "var x = 1;\n"
        let actual = ensureSameLineCount "if (true) ; else return;" "if \n(true) \n;\n else\n return;\n"
        let expected = "if (true) ; else return;\n\n\n\n"

        actual =? expected

[<TestFixture>]
module ``AutoProperty method`` =
    [<Test>]
    let ``throws when property name is null`` () =
        raisesArgumentNullException "propertyName" <@ Syntax.AutoProperty null "int" Public None None @>

    [<Test>]
    let ``throws when property name is empty`` () =
        raisesArgumentException "propertyName" <@ Syntax.AutoProperty "  " "int" Public None None @>

    [<Test>]
    let ``throws when property type is null`` () =
        raisesArgumentNullException "propertyType" <@ Syntax.AutoProperty "Name" null Public None None @>

    [<Test>]
    let ``throws when property type is empty`` () =
        raisesArgumentException "propertyType" <@ Syntax.AutoProperty "Name" "  " Public None None @>

    [<Test>]
    let ``throws when visibility modifiers are specified for both accessors`` () =
        raises<InvalidOperationException> <@ Syntax.AutoProperty "Name" "int" Public (Some Public) (Some Public) @>

    [<Test>]
    let ``creates property without accessor visibility modifiers`` () =
        toString (Syntax.AutoProperty "Name" "int" Public None None) =? "public int Name { get; set; }"
        toString (Syntax.AutoProperty "Name" "int" Internal None None) =? "internal int Name { get; set; }"
        toString (Syntax.AutoProperty "Name" "int" ProtectedInternal None None) =? "protected internal int Name { get; set; }"
        toString (Syntax.AutoProperty "Name" "int" Protected None None) =? "protected int Name { get; set; }"
        toString (Syntax.AutoProperty "Name" "int" Private None None) =? "private int Name { get; set; }"

    [<Test>]
    let ``creates property with visibility modifier for get accessor`` () =
        toString (Syntax.AutoProperty "Name" "int" Internal (Some Private) None) =? "internal int Name { private get; set; }"
        toString (Syntax.AutoProperty "Name" "int" Public (Some Private) None) =? "public int Name { private get; set; }"
        toString (Syntax.AutoProperty "Name" "int" Public (Some Internal) None) =? "public int Name { internal get; set; }"

    [<Test>]
    let ``creates property with visibility modifier for set accessor`` () =
        toString (Syntax.AutoProperty "Name" "int" Internal None (Some Private)) =? "internal int Name { get; private set; }"
        toString (Syntax.AutoProperty "Name" "int" Public None (Some Private)) =? "public int Name { get; private set; }"
        toString (Syntax.AutoProperty "Name" "int" Public None (Some Internal)) =? "public int Name { get; internal set; }"

[<TestFixture>]
module ``Lambda method`` =
    [<Test>]
    let ``throws when body is null`` () =
        raisesArgumentNullException "body" <@ Syntax.Lambda [] null @>

    [<Test>]
    let ``creates lambda with empty argument list`` () =
        toString (Syntax.Lambda [] (SyntaxFactory.ParseExpression "1 + 1")) =? "() => 1 + 1"
        toString (Syntax.Lambda [] (SyntaxFactory.ParseStatement "{ var i = 1; return 1 + i; }")) =? "() => { var i = 1; return 1 + i; }"

    [<Test>]
    let ``creates simple lambda with single argument`` () =
        let parameterSyntax = SyntaxFactory.Parameter (SyntaxFactory.Identifier "x")
        toString (Syntax.Lambda [parameterSyntax] (SyntaxFactory.ParseExpression "x + 1")) =? "x => x + 1"
        toString (Syntax.Lambda [parameterSyntax] (SyntaxFactory.ParseStatement "{ var i = 1; return x + i; }")) =? "x => { var i = 1; return x + i; }"

    [<Test>]
    let ``creates lambda with single argument`` () =
        let parameterSyntax = SyntaxFactory.Parameter(SyntaxFactory.Identifier "x").WithType (SyntaxFactory.ParseTypeName "int")
        toString (Syntax.Lambda [parameterSyntax] (SyntaxFactory.ParseExpression "x + 1")) =? "(int x) => x + 1"
        toString (Syntax.Lambda [parameterSyntax] (SyntaxFactory.ParseStatement "{ var i = 1; return x + i; }")) =? "(int x) => { var i = 1; return x + i; }"

    [<Test>]
    let ``creates lambda with multiple argument`` () =
        let parameterSyntax1 = SyntaxFactory.Parameter(SyntaxFactory.Identifier "x").WithType (SyntaxFactory.ParseTypeName "int")
        let parameterSyntax2 = SyntaxFactory.Parameter(SyntaxFactory.Identifier "y").WithType (SyntaxFactory.ParseTypeName "int")
        let parameterSyntax3 = SyntaxFactory.Parameter(SyntaxFactory.Identifier "z").WithType (SyntaxFactory.ParseTypeName "bool")
        let parameters1 = [parameterSyntax1; parameterSyntax2]
        let parameters2 = [parameterSyntax1; parameterSyntax2; parameterSyntax3]

        toString (Syntax.Lambda parameters1 (SyntaxFactory.ParseExpression "x + y")) =? "(int x, int y) => x + y"
        toString (Syntax.Lambda parameters2 (SyntaxFactory.ParseStatement "{ var i = x; return i == y || z; }")) =? 
            "(int x, int y, bool z) => { var i = x; return i == y || z; }"