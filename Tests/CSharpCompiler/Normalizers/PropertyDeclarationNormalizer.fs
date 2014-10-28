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
module PropertyDeclarationNormalizer =
    let normalizeClass csharpCode = 
        TestCompilation.GetNormalizedClass (PropertyDeclarationNormalizer()) 
            (csharpCode + "interface IGet { bool B { get; } } interface ISet { bool B { set; } } interface IGetSet { bool B { get; set; } }")

    let normalizeInterface csharpCode = 
        TestCompilation.GetNormalizedInterface (PropertyDeclarationNormalizer()) csharpCode

    let getterName propertyName =
        IdentifierNameSynthesizer.ToSynthesizedName <| sprintf "Get%s" propertyName

    let setterName propertyName =
        IdentifierNameSynthesizer.ToSynthesizedName <| sprintf "Set%s" propertyName

    [<Test>]
    let ``does not normalize properties of non-component classes`` () =
        normalizeClass "class X { bool B { get { return false; } } }" =? "class X { bool B { get { return false; } } }"

    [<Test>]
    let ``does not normalize properties of non-component interfaces`` () =
        normalizeInterface "interface X { bool B { get; } }" =? "interface X { bool B { get; } }"

    [<Test>]
    let ``normalizes getter-only class property`` () =
        normalizeClass "class X : Component { bool B { get { return false; } } }" =? 
            sprintf "class X : Component { bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { internal protected int B { get { return 0; } } }" =? 
            sprintf "class X : Component { internal protected int %s() { return 0; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only class property`` () =
        normalizeClass "class X : Component { bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { internal protected int B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { internal protected void %s(int value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes class property with both getter and setter`` () =
        normalizeClass "class X : Component { bool B { get { return true; } set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { bool %s() { return true; } void %s(bool value) { System.Console.WriteLine(value); } }" 
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { public int B { get { return 1; } set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { public int %s() { return 1; } public void %s(int value) { System.Console.WriteLine(value); } }" 
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only class property with property attribute`` () =
        normalizeClass "class X : Component { [Required] public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { [Required, Provided] public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { [Required] [Provided] public bool B { get { return false; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only class property with property attribute`` () =
        normalizeClass "class X : Component { [Required] public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { [Required, Provided] public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required, Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { [Required] [Provided] public bool B { set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes class property with getter and setter and property attribute`` () =
        normalizeClass "class X : Component { [Required] public bool B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } [Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { [Required, Provided] public bool B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } [Required, Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { [Required] [Provided] public bool B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } [Required] [Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only class property with getter attribute`` () =
        normalizeClass "class X : Component { public bool B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { public bool B { [Required, Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { public bool B { [Required] [Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only class property with setter attribute`` () =
        normalizeClass "class X : Component { public bool B { [Required] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { public bool B { [Required, Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required, Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { public bool B { [Required] [Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes class property with getter and setter and getter and setter attributes`` () =
        normalizeClass "class X : Component { public bool B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] public bool %s() { return false; } [Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { public bool B { [Required, Provided] get { return false; } [Provided, Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required, Provided] public bool %s() { return false; } [Provided, Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { public bool B { [Required] [Provided] get { return false; } [Provided] [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] public bool %s() { return false; } [Provided] [Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only class property with getter and property attributes`` () =
        normalizeClass "class X : Component { [Provided] public bool B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component { [Provided] [Required] public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { [Required, Provided] public bool B { [Required, Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required, Provided] [Required, Provided] public bool %s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component { [Required] [Provided] public bool B { [Required] [Provided] get { return false; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] [Required] [Provided] public bool %s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes setter-only class property with setter and property attributes`` () =
        normalizeClass "class X : Component { [Required] public bool B { [Required] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Required] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { [Required, Provided] public bool B { [Required, Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required, Provided] [Required, Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")
        normalizeClass "class X : Component { [Required] [Provided] public bool B { [Required] [Provided] set { System.Console.WriteLine(value); } } }" =? 
            sprintf "class X : Component { [Required] [Provided] [Required] [Provided] public void %s(bool value) { System.Console.WriteLine(value); } }" (setterName "B")

    [<Test>]
    let ``normalizes class property with getter and setter as well as getter and setter and property attributes`` () =
        normalizeClass "class X : Component { [Required] public bool B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Required] public bool %s() { return false; } [Required] [Provided] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { [Required, Provided] public bool B { [Required, Provided] get { return false; } [Provided, Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required, Provided] [Required, Provided] public bool %s() { return false; } [Required, Provided] [Provided, Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component { [Required] [Provided] public bool B { [Required] [Provided] get { return false; } [Provided] [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component { [Required] [Provided] [Required] [Provided] public bool %s() { return false; } [Required] [Provided] [Provided] [Required] public void %s(bool value) { var x = value; } }"
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes explicitly implemented getter-only class property`` () =
        normalizeClass "class X : Component, IGet { bool IGet.B { get { return false; } } }" =? 
            sprintf "class X : Component, IGet { bool IGet.%s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component, IGet { [Provided] bool IGet.B { get { return false; } } }" =? 
            sprintf "class X : Component, IGet { [Provided] bool IGet.%s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component, IGet { bool IGet.B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component, IGet { [Required] bool IGet.%s() { return false; } }" (getterName "B")
        normalizeClass "class X : Component, IGet { [Provided] bool IGet.B { [Required] get { return false; } } }" =? 
            sprintf "class X : Component, IGet { [Provided] [Required] bool IGet.%s() { return false; } }" (getterName "B")

    [<Test>]
    let ``normalizes explicitly implemented setter-only class property`` () =
        normalizeClass "class X : Component, ISet { bool ISet.B { set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { void ISet.%s(bool value) { var x = value; } }" (setterName "B")
        normalizeClass "class X : Component, ISet { [Provided] bool ISet.B { set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { [Provided] void ISet.%s(bool value) { var x = value; } }" (setterName "B")
        normalizeClass "class X : Component, ISet { bool ISet.B { [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { [Required] void ISet.%s(bool value) { var x = value; } }" (setterName "B")
        normalizeClass "class X : Component, ISet { [Provided] bool ISet.B { [Required] set { var x = value; } } }" =? 
            sprintf "class X : Component, ISet { [Provided] [Required] void ISet.%s(bool value) { var x = value; } }" (setterName "B")

    [<Test>]
    let ``normalizes explicitly implemented class property with getter and setter`` () =
        normalizeClass "class X : Component, IGetSet { bool IGetSet.B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { bool IGetSet.%s() { return false; } void IGetSet.%s(bool value) { var x = value; } }" 
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component, IGetSet { [Provided] bool IGetSet.B { get { return false; } set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { [Provided] bool IGetSet.%s() { return false; } [Provided] void IGetSet.%s(bool value) { var x = value; } }" 
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component, IGetSet { bool IGetSet.B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { [Required] bool IGetSet.%s() { return false; } [Provided] void IGetSet.%s(bool value) { var x = value; } }" 
                (getterName "B") (setterName "B")
        normalizeClass "class X : Component, IGetSet { [Provided] bool IGetSet.B { [Required] get { return false; } [Provided] set { var x = value; } } }" =? 
            sprintf "class X : Component, IGetSet { [Provided] [Required] bool IGetSet.%s() { return false; } [Provided] [Provided] void IGetSet.%s(bool value) { var x = value; } }"  
                (getterName "B") (setterName "B")

    [<Test>]
    let ``normalizes getter-only interface property`` () =
        normalizeInterface "interface I : IComponent { int X { get; } }" =? 
            sprintf "interface I : IComponent { int %s(); }" (getterName "X")

    [<Test>]
    let ``normalizes setter-only interface property`` () =
        normalizeInterface "interface I : IComponent { int X { set; } }" =? 
            sprintf "interface I : IComponent { void %s(int value); }" (setterName "X")

    [<Test>]
    let ``normalizes interface property with getter and setter`` () =
        normalizeInterface "interface I : IComponent { int X { get; set; } }" =? 
            sprintf "interface I : IComponent { int %s(); void %s(int value); }" (getterName "X") (setterName "X")

    [<Test>]
    let ``normalizes getter-only interface property with property attributes`` () =
        normalizeInterface "interface I : IComponent { [Provided] int X { get; } }" =? 
            sprintf "interface I : IComponent { [Provided] int %s(); }" (getterName "X")
        normalizeInterface "interface I : IComponent { [Provided] [Required] int X { get; } }" =? 
            sprintf "interface I : IComponent { [Provided] [Required] int %s(); }" (getterName "X")
        normalizeInterface "interface I : IComponent { [Provided, Required] int X { get; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] int %s(); }" (getterName "X")

    [<Test>]
    let ``normalizes setter-only interface property with property attributes`` () =
        normalizeInterface "interface I : IComponent { [Provided] int X { set; } }" =? 
            sprintf "interface I : IComponent { [Provided] void %s(int value); }" (setterName "X")
        normalizeInterface "interface I : IComponent { [Provided] [Required] int X { set; } }" =? 
            sprintf "interface I : IComponent { [Provided] [Required] void %s(int value); }" (setterName "X")
        normalizeInterface "interface I : IComponent { [Provided, Required] int X { set; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] void %s(int value); }" (setterName "X")

    [<Test>]
    let ``normalizes getter-only interface property with getter attributes`` () =
        normalizeInterface "interface I : IComponent { int X { [Provided] get; } }" =? 
            sprintf "interface I : IComponent { [Provided] int %s(); }" (getterName "X")
        normalizeInterface "interface I : IComponent { int X { [Provided] [Required] get; } }" =? 
            sprintf "interface I : IComponent { [Provided] [Required] int %s(); }" (getterName "X")
        normalizeInterface "interface I : IComponent { int X { [Provided, Required] get; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] int %s(); }" (getterName "X")

    [<Test>]
    let ``normalizes setter-only interface property with setter attributes`` () =
        normalizeInterface "interface I : IComponent { int X { [Provided] set; } }" =? 
            sprintf "interface I : IComponent { [Provided] void %s(int value); }" (setterName "X")
        normalizeInterface "interface I : IComponent { int X { [Provided] [Required] set; } }" =? 
            sprintf "interface I : IComponent { [Provided] [Required] void %s(int value); }" (setterName "X")
        normalizeInterface "interface I : IComponent { int X { [Provided, Required] set; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] void %s(int value); }" (setterName "X")

    [<Test>]
    let ``normalizes getter-only interface property with getter and property attributes`` () =
        normalizeInterface "interface I : IComponent { [Required] int X { [Provided] get; } }" =? 
            sprintf "interface I : IComponent { [Required] [Provided] int %s(); }" (getterName "X")
        normalizeInterface "interface I : IComponent { [Provided, Required] int X { [Provided] [Required] get; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] [Provided] [Required] int %s(); }" (getterName "X")
        normalizeInterface "interface I : IComponent { [Required] int X { [Provided, Required] get; } }" =? 
            sprintf "interface I : IComponent { [Required] [Provided, Required] int %s(); }" (getterName "X")

    [<Test>]
    let ``normalizes setter-only interface property with setter and property attributes`` () =
        normalizeInterface "interface I : IComponent { [Required] int X { [Provided] set; } }" =? 
            sprintf "interface I : IComponent { [Required] [Provided] void %s(int value); }" (setterName "X")
        normalizeInterface "interface I : IComponent { [Provided, Required] int X { [Provided] [Required] set; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] [Provided] [Required] void %s(int value); }" (setterName "X")
        normalizeInterface "interface I : IComponent { [Required] int X { [Provided, Required] set; } }" =? 
            sprintf "interface I : IComponent { [Required] [Provided, Required] void %s(int value); }" (setterName "X")

    [<Test>]
    let ``normalizes interface property with getter and setter as well as attributes`` () =
        normalizeInterface "interface I : IComponent { [Provided] int X { get; [Required] set; } }" =? 
            sprintf "interface I : IComponent { [Provided] int %s(); [Provided] [Required] void %s(int value); }" (getterName "X") (setterName "X")
        normalizeInterface "interface I : IComponent { [Provided, Required] int X { [Provided] get; [Required] set; } }" =? 
            sprintf "interface I : IComponent { [Provided, Required] [Provided] int %s(); [Provided, Required] [Required] void %s(int value); }" (getterName "X") (setterName "X")