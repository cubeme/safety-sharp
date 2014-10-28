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
module ClassPropertyDeclarationNormalizer =
    let normalize csharpCode = 
        TestCompilation.GetNormalizedClass (ClassPropertyDeclarationNormalizer()) 
            (csharpCode + "interface IGet { bool B { get; } } interface ISet { bool B { set; } } interface IGetSet { bool B { get; set; } }")

    let getterName propertyName =
        IdentifierNameSynthesizer.ToSynthesizedName <| sprintf "Get%s" propertyName

    let setterName propertyName =
        IdentifierNameSynthesizer.ToSynthesizedName <| sprintf "Set%s" propertyName

    [<Test>]
    let ``does not normalize properties of non-component classes`` () =
        normalize "class X { bool B { get { return false; } } }" =? "class X { bool B { get { return false; } } }"

    [<Test>]
    let ``normalizes getter-only property`` () =
        normalize "class X : Component { bool B { get { return false; } } }" =? 
            sprintf "class X : Component { bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { internal protected int B { get { return 0; } } }" =? 
            sprintf "class X : Component { internal protected int %s() { return 0; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only property`` () =
        normalize "class X : Component { bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { internal protected int B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { internal protected void %s(int value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes property with both getter and setter`` () =
        normalize "class X : Component { bool B { get { return true; } set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { bool %s() { return true; } void %s(bool value) { System.Console.WriteLine(value); } }" 
                (getterName "B") (setterName "B")
        normalize "class X : Component { public int B { get { return 1; } set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { public int %s() { return 1; } public void %s(int value) { System.Console.WriteLine(value); } }" 
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only property with property attribute`` () =
        normalize "class X : Component { [Required] public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { [Required, Provided] public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { [Required] [Provided] public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only property with property attribute`` () =
        normalize "class X : Component { [Required] public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { [Required, Provided] public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required, Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { [Required] [Provided] public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes property with getter and setter and property attribute`` () =
        normalize "class X : Component { [Required] public bool B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } [Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalize "class X : Component { [Required, Provided] public bool B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } [Required, Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalize "class X : Component { [Required] [Provided] public bool B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } [Required] [Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only property with getter attribute`` () =
        normalize "class X : Component { public bool B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { public bool B { [Required, Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { public bool B { [Required] [Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only property with setter attribute`` () =
        normalize "class X : Component { public bool B { [Required] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { public bool B { [Required, Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required, Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { public bool B { [Required] [Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes property with getter and setter and getter and setter attributes`` () =
        normalize "class X : Component { public bool B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } [Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalize "class X : Component { public bool B { [Required, Provided] get { return false; } [Provided, Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } [Provided, Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalize "class X : Component { public bool B { [Required] [Provided] get { return false; } [Provided] [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } [Provided] [Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only property with getter and property attributes`` () =
        normalize "class X : Component { [Provided] public bool B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component { [Provided] [Required] public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { [Required, Provided] public bool B { [Required, Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required, Provided] [Required, Provided] public bool %s() { return false; } }" (getterName "B")
        normalize "class X : Component { [Required] [Provided] public bool B { [Required] [Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] [Required] [Provided] public bool %s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only property with setter and property attributes`` () =
        normalize "class X : Component { [Required] public bool B { [Required] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Required] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { [Required, Provided] public bool B { [Required, Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required, Provided] [Required, Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalize "class X : Component { [Required] [Provided] public bool B { [Required] [Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Provided] [Required] [Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes property with getter and setter as well as getter and setter and property attributes`` () =
        normalize "class X : Component { [Required] public bool B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Required] public bool %s() { return false; } [Required] [Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalize "class X : Component { [Required, Provided] public bool B { [Required, Provided] get { return false; } [Provided, Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required, Provided] [Required, Provided] public bool %s() { return false; } [Required, Provided] [Provided, Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalize "class X : Component { [Required] [Provided] public bool B { [Required] [Provided] get { return false; } [Provided] [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] [Required] [Provided] public bool %s() { return false; } [Required] [Provided] [Provided] [Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes explicitly implemented getter-only property`` () =
        normalize "class X : Component, IGet { bool IGet.B { get { return false; } } }" =? 
            sprintf "class X : Component, IGet { bool IGet.%s() { return false; } }" (getterName "B")
        normalize "class X : Component, IGet { [Provided] bool IGet.B { get { return false; } } }" =? 
            sprintf "class X : Component, IGet { [Provided] bool IGet.%s() { return false; } }" (getterName "B")
        normalize "class X : Component, IGet { bool IGet.B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component, IGet { [Required] bool IGet.%s() { return false; } }" (getterName "B")
        normalize "class X : Component, IGet { [Provided] bool IGet.B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component, IGet { [Provided] [Required] bool IGet.%s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes explicitly implemented setter-only property`` () =
        normalize "class X : Component, ISet { bool ISet.B { set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { void ISet.%s(bool value) { var x = value; } }" (setterName "B")
        normalize "class X : Component, ISet { [Provided] bool ISet.B { set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { [Provided] void ISet.%s(bool value) { var x = value; } }" (setterName "B")
        normalize "class X : Component, ISet { bool ISet.B { [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { [Required] void ISet.%s(bool value) { var x = value; } }" (setterName "B")
        normalize "class X : Component, ISet { [Provided] bool ISet.B { [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { [Provided] [Required] void ISet.%s(bool value) { var x = value; } }" (setterName "B")

    [<Test>]
    let ``normalizes explicitly implemented property with getter and setter`` () =
        normalize "class X : Component, IGetSet { bool IGetSet.B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { bool IGetSet.%s() { return false; } void IGetSet.%s(bool value) { var x = value; } }" 
                (getterName "B") (setterName "B")
        normalize "class X : Component, IGetSet { [Provided] bool IGetSet.B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { [Provided] bool IGetSet.%s() { return false; } [Provided] void IGetSet.%s(bool value) { var x = value; } }" 
                (getterName "B") (setterName "B")
        normalize "class X : Component, IGetSet { bool IGetSet.B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { [Required] bool IGetSet.%s() { return false; } [Provided] void IGetSet.%s(bool value) { var x = value; } }" 
                (getterName "B") (setterName "B")
        normalize "class X : Component, IGetSet { [Provided] bool IGetSet.B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { [Provided] [Required] bool IGetSet.%s() { return false; } [Provided] [Provided] void IGetSet.%s(bool value) { var x = value; } }"  
                (getterName "B") (setterName "B")