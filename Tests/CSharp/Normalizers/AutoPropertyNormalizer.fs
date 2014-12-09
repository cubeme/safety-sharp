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

namespace Normalization

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Tests
open SafetySharp.Modeling
open SafetySharp.CSharpCompiler.Normalization
open SafetySharp.CSharpCompiler.Roslyn
open SafetySharp.CSharpCompiler.Roslyn.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols

[<TestFixture>]
module AutoPropertyNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (AutoPropertyNormalizer()) 
            (csharpCode + "interface I { int B { get; set; } } namespace N { interface I { int B { get; set; } } }")

    let fieldName propertyName =
        IdentifierNameSynthesizer.ToSynthesizedName <| sprintf "BackingField_%s" propertyName

    let fieldInterfaceName (interfaceName : string) propertyName =
        IdentifierNameSynthesizer.ToSynthesizedName <| sprintf "%s_BackingField_%s" (interfaceName.Replace(".", "_")) propertyName

    [<Test>]
    let ``does not normalize properties of non-component classes`` () =
        normalize "class X { bool B { get; set; } }" =? "class X { bool B { get; set; } }"

    [<Test>]
    let ``does not normalize properties with expression bodies`` () =
        normalize "class X : Component { bool B => false; }" =? "class X : Component { bool B => false; }"

    [<Test>]
    let ``does not normalize properties with accessor bodies`` () =
        normalize "class X : Component { bool B { get { return true; } } }" =? "class X : Component { bool B { get { return true; } } }"
        normalize "class X : Component { bool B { set { var x = value; } } }" =? "class X : Component { bool B { set { var x = value; } } }"
        normalize "class X : Component { bool B { get { return false; } set { var x = value; } } }" =? 
            "class X : Component { bool B { get { return false; } set { var x = value; } } }"

    [<Test>]
    let ``normalizes property without attributes`` () =
        normalize "class X : Component { bool B { get; set; } }" =? 
            sprintf "class X : Component { private bool %s; bool B { get { return %s; } set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { protected internal bool B { get; set; } }" =? 
            sprintf "class X : Component { private bool %s; protected internal bool B { get { return %s; } set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")

    [<Test>]
    let ``normalizes property with attributes`` () =
        normalize "class X : Component { [Required] bool B { get; set; } }" =? 
            sprintf "class X : Component { private bool %s; [Required] bool B { get { return %s; } set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { bool B { [Required] get; set; } }" =? 
            sprintf "class X : Component { private bool %s; bool B { [Required] get { return %s; } set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { bool B { get; [Required] set; } }" =? 
            sprintf "class X : Component { private bool %s; bool B { get { return %s; } [Required] set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { [Provided] bool B { [Provided] get; [Required] set; } }" =? 
            sprintf "class X : Component { private bool %s; [Provided] bool B { [Provided] get { return %s; } [Required] set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { bool B { [Required, Provided] get; set; } }" =? 
            sprintf "class X : Component { private bool %s; bool B { [Required, Provided] get { return %s; } set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { bool B { get; [Required, Provided] set; } }" =? 
            sprintf "class X : Component { private bool %s; bool B { get { return %s; } [Required, Provided] set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")
        normalize "class X : Component { [Provided] [Required] bool B { [Provided] get; [Required, Provided] set; } }" =? 
            sprintf "class X : Component { private bool %s; [Provided] [Required] bool B { [Provided] get { return %s; } [Required, Provided] set { %s = value; } } }" 
                (fieldName "B") (fieldName "B") (fieldName "B")

    [<Test>]
    let ``normalizes explicitly implemented property without attributes`` () =
        normalize "class X : Component, I { int I.B { get; set; } }" =? 
            sprintf "class X : Component, I { private int %s; int I.B { get { return %s; } set { %s = value; } } }" 
                (fieldInterfaceName "I" "B") (fieldInterfaceName "I" "B") (fieldInterfaceName "I" "B")
        normalize "class X : Component, N.I { int N.I.B { get; set; } }" =? 
            sprintf "class X : Component, N.I { private int %s; int N.I.B { get { return %s; } set { %s = value; } } }" 
                (fieldInterfaceName "N.I" "B") (fieldInterfaceName "N.I" "B") (fieldInterfaceName "N.I" "B")

    [<Test>]
    let ``normalizes explicitly implemented property with attributes`` () =
        normalize "class X : Component, I { [Required] int I.B { get; [Provided, Required] set; } }" =? 
            sprintf "class X : Component, I { private int %s; [Required] int I.B { get { return %s; } [Provided, Required] set { %s = value; } } }" 
                (fieldInterfaceName "I" "B") (fieldInterfaceName "I" "B") (fieldInterfaceName "I" "B")
