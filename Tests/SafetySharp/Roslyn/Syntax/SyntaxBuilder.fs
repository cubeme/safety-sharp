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

namespace Roslyn.Syntax.SyntaxBuilder

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Compiler.Roslyn.Syntax
open SafetySharp.Compiler.Roslyn.Symbols

[<AutoOpen>]
module SyntaxTestsHelpers =
    let toString (node : SyntaxNode) =
        node.ToFullString().Replace ("\r", String.Empty)

[<TestFixture>]
module ``AutoProperty method`` =
    [<Test>]
    let ``throws when property name is null`` () =
        raisesArgumentNullException "propertyName" 
            (fun () -> SyntaxBuilder.AutoProperty (null, "int", Visibility.Public, Nullable (), Nullable ()) |> ignore)

    [<Test>]
    let ``throws when property name is empty`` () =
        raisesArgumentException "propertyName" 
            (fun () -> SyntaxBuilder.AutoProperty ("  ", "int", Visibility.Public, Nullable (), Nullable ()) |> ignore)

    [<Test>]
    let ``throws when property type is null`` () =
        raisesArgumentNullException "propertyType" 
            (fun () -> SyntaxBuilder.AutoProperty ("Name", null, Visibility.Public, Nullable (), Nullable ()) |> ignore)

    [<Test>]
    let ``throws when property type is empty`` () =
        raisesArgumentException "propertyType" 
            (fun () -> SyntaxBuilder.AutoProperty ("Name", "  ", Visibility.Public, Nullable (), Nullable ()) |> ignore)

    [<Test>]
    let ``throws when visibility modifiers are specified for both accessors`` () =
        raises<InvalidOperationException> 
            (fun () -> SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Public, Nullable (Visibility.Public), Nullable (Visibility.Public)) 
                       |> ignore)

    [<Test>]
    let ``creates property without accessor visibility modifiers`` () =
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Public, Nullable (), Nullable ()))
            =? "public int Name { get; set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Internal, Nullable (), Nullable ())) 
            =? "internal int Name { get; set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.ProtectedInternal, Nullable (), Nullable ()))
            =? "protected internal int Name { get; set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Protected, Nullable (), Nullable ()))
            =? "protected int Name { get; set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Private, Nullable (), Nullable ()))
            =? "private int Name { get; set; }"

    [<Test>]
    let ``creates property with visibility modifier for get accessor`` () =
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Internal, Nullable (Visibility.Private), Nullable ())) 
            =? "internal int Name { private get; set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Public, Nullable (Visibility.Private), Nullable ())) 
            =? "public int Name { private get; set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Public, Nullable (Visibility.Internal), Nullable ())) 
            =? "public int Name { internal get; set; }"

    [<Test>]
    let ``creates property with visibility modifier for set accessor`` () =
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Internal, Nullable (), Nullable (Visibility.Private))) 
            =? "internal int Name { get; private set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Public, Nullable (), Nullable (Visibility.Private))) 
            =? "public int Name { get; private set; }"
        toString (SyntaxBuilder.AutoProperty ("Name", "int", Visibility.Public, Nullable (), Nullable (Visibility.Internal))) 
            =? "public int Name { get; internal set; }"

[<TestFixture>]
module ``InterfaceProperty method`` =
    [<Test>]
    let ``throws when property name is null`` () =
        raisesArgumentNullException "propertyName" (fun () -> SyntaxBuilder.InterfaceProperty (null, "int", true, true) |> ignore)

    [<Test>]
    let ``throws when property name is empty`` () =
        raisesArgumentException "propertyName" (fun () -> SyntaxBuilder.InterfaceProperty ("  ", "int", true, true) |> ignore)

    [<Test>]
    let ``throws when property type is null`` () =
        raisesArgumentNullException "propertyType" (fun () -> SyntaxBuilder.InterfaceProperty ("Name", null, true, true) |> ignore)

    [<Test>]
    let ``throws when property type is empty`` () =
        raisesArgumentException "propertyType" (fun () -> SyntaxBuilder.InterfaceProperty ("Name", "  ", true, true) |> ignore)

    [<Test>]
    let ``throws when property has no accessor`` () =
        raises<InvalidOperationException> (fun () -> SyntaxBuilder.InterfaceProperty ("Name", "int", false, false) |> ignore)

    [<Test>]
    let ``creates get-only property`` () =
        toString (SyntaxBuilder.InterfaceProperty ("Name", "int", true, false)) =? "int Name { get; }"

    [<Test>]
    let ``creates set-only property`` () =
        toString (SyntaxBuilder.InterfaceProperty ("Name", "int", false, true)) =? "int Name { set; }"

    [<Test>]
    let ``creates get/set property`` () =
        toString (SyntaxBuilder.InterfaceProperty ("Name", "int", true, true)) =? "int Name { get; set; }"

[<TestFixture>]
module ``Lambda method`` =
    [<Test>]
    let ``throws when body is null`` () =
        raisesArgumentNullException "body" (fun () -> SyntaxBuilder.Lambda ([], null) |> ignore)

    [<Test>]
    let ``creates lambda with empty argument list`` () =
        toString (SyntaxBuilder.Lambda ([], (SyntaxFactory.ParseExpression "1 + 1"))) 
            =? "() => 1 + 1"
        toString (SyntaxBuilder.Lambda ([], (SyntaxFactory.ParseStatement "{ var i = 1; return 1 + i; }"))) 
            =? "() => { var i = 1; return 1 + i; }"

    [<Test>]
    let ``creates simple lambda with single argument`` () =
        let parameterSyntax = SyntaxFactory.Parameter (SyntaxFactory.Identifier "x")
        toString (SyntaxBuilder.Lambda ([parameterSyntax], (SyntaxFactory.ParseExpression "x + 1"))) 
            =? "x => x + 1"
        toString (SyntaxBuilder.Lambda ([parameterSyntax], (SyntaxFactory.ParseStatement "{ var i = 1; return x + i; }")))
            =? "x => { var i = 1; return x + i; }"

    [<Test>]
    let ``creates lambda with single argument`` () =
        let parameterSyntax = SyntaxFactory.Parameter(SyntaxFactory.Identifier "x").WithType (SyntaxFactory.ParseTypeName "int")
        toString (SyntaxBuilder.Lambda ([parameterSyntax], (SyntaxFactory.ParseExpression "x + 1"))) 
            =? "(int x) => x + 1"
        toString (SyntaxBuilder.Lambda ([parameterSyntax], (SyntaxFactory.ParseStatement "{ var i = 1; return x + i; }"))) 
            =? "(int x) => { var i = 1; return x + i; }"

    [<Test>]
    let ``creates lambda with multiple argument`` () =
        let parameterSyntax1 = SyntaxFactory.Parameter(SyntaxFactory.Identifier "x").WithType (SyntaxFactory.ParseTypeName "int")
        let parameterSyntax2 = SyntaxFactory.Parameter(SyntaxFactory.Identifier "y").WithType (SyntaxFactory.ParseTypeName "int")
        let parameterSyntax3 = SyntaxFactory.Parameter(SyntaxFactory.Identifier "z").WithType (SyntaxFactory.ParseTypeName "bool")
        let parameters1 = [parameterSyntax1; parameterSyntax2]
        let parameters2 = [parameterSyntax1; parameterSyntax2; parameterSyntax3]

        toString (SyntaxBuilder.Lambda (parameters1, (SyntaxFactory.ParseExpression "x + y"))) 
            =? "(int x, int y) => x + y"
        toString (SyntaxBuilder.Lambda (parameters2, (SyntaxFactory.ParseStatement "{ var i = x; return i == y || z; }"))) 
            =? "(int x, int y, bool z) => { var i = x; return i == y || z; }"