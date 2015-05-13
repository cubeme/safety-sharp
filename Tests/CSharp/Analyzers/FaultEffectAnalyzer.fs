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

namespace Analyzers

open System
open System.Linq
open NUnit.Framework
open SafetySharp.Modeling
open SafetySharp.CSharp.Analyzers
open SafetySharp.CSharp.Roslyn.Syntax
open SafetySharp.CSharp.Roslyn.Symbols

[<TestFixture>]
module ``Fault effects`` =
    let getDiagnostic csharpCode = 
        let csharpCode = 
            sprintf "
                class X : Y { 
                    public void Void2Void() { }
                    public int Int2Int(int x) { return x; }
                    public void Overloaded(int x) { }
                    public void Overloaded() { }
                    public void Overloaded(bool b) { }
                    public void Ref(ref int x) { }
                    public void Out(out int x) { x = 1; }
                    public void Optional(int x = 3) { }
                    public int GetProp => 1;
                    public int SetProp { set { } }
                    public int Prop { get; set; }
                    public int get_GetMethodProp() => 1;
                    public void set_SetMethodProp(int value) { }
                    [Transient] class F : Fault { %s }
                }
                class Y : Component { 
                    public void Inherited() { }
                    private void Inaccessible() { }
                    public int InheritedProp => 1;
                    private int InaccessibleProp => 1;
                }
            " csharpCode
        TestCompilation.GetDiagnostic (FaultEffectAnalyzer ()) csharpCode

    let getLocation location = location + 50
    let line = 16

    let unknownMethodPort location memberName effect =
        errorDiagnostic DiagnosticIdentifier.FaultEffectUnknownMethodPort (line, getLocation location) (line, getLocation location + (String.length memberName))
            "Invalid fault method '%s': Affected component of type 'X' does not declare a method named '%s'." effect memberName

    let unknownPropertyPort location memberName effect =
        errorDiagnostic DiagnosticIdentifier.FaultEffectUnknownPropertyPort (line, getLocation location) (line, getLocation location + (String.length memberName))
            "Invalid fault property '%s': Affected component of type 'X' does not declare a property named '%s' with the corresponding accessors." effect memberName

    let signatureIncompatible location memberName effect portName =
        errorDiagnostic DiagnosticIdentifier.FaultEffectSignatureIncompatible (line, getLocation location) (line, getLocation location + (String.length memberName))
            "Fault effect '%s' is not signature compatible with '%s' or any of its overloads." effect portName

    let optionalParameter location effect parameterName =
        errorDiagnostic DiagnosticIdentifier.FaultEffectOptionalParameter (line, getLocation location) (line, getLocation location + (String.length parameterName))
            "Invalid optional parameter '%s' declared by fault effect '%s'." parameterName effect

    let baseMember location memberName effect baseClass =
        errorDiagnostic DiagnosticIdentifier.FaultEffectBaseMember (line, getLocation location) (line, getLocation location + (String.length memberName))
            "Fault effect '%s' cannot affect inherited member '%s'." effect baseClass

    let propertyType location memberName effect propertyType =
        errorDiagnostic DiagnosticIdentifier.FaultEffectIncompatibleType (line, getLocation location) (line, getLocation location + (String.length memberName))
            "Fault effect '%s' must be a property of type '%s'." effect propertyType

    [<Test>]
    let ``fault class without effects is valid`` () =
        getDiagnostic "" =? None

    [<Test>]
    let ``non-nested fault class is valid`` () =
        TestCompilation.GetDiagnostic (FaultEffectAnalyzer ()) "[Transient] class F : Fault { public void M() {} }" =? None

    [<Test>]
    let ``fault class nested in non-component class is valid`` () =
        TestCompilation.GetDiagnostic (FaultEffectAnalyzer ()) "class X { [Transient] class F : Fault { public void M() {} }}" =? None

    [<Test>]
    let ``fault effect for unknown port is invalid`` () =
        getDiagnostic "public void Q() {}" =? unknownMethodPort 12 "Q" "X.F.Q()" 

    [<Test>]
    let ``fault effect for signature compatible port is valid`` () =
        getDiagnostic "public void Void2Void() { }" =? None
        getDiagnostic "public int Int2Int(int a) { return a; }" =? None
        getDiagnostic "public void Overloaded(int b) { }" =? None
        getDiagnostic "public void Overloaded() { }" =? None
        getDiagnostic "public void Overloaded(bool d) { }" =? None
        getDiagnostic "public void Ref(ref int q) { }" =? None
        getDiagnostic "public void Out(out int q) { q = 1; }" =? None

    [<Test>]
    let ``fault effect for property port getter or setter with same type is valid`` () =
        getDiagnostic "public int GetProp => 1;" =? None
        getDiagnostic "public int SetProp { set { } }" =? None
        getDiagnostic "public int Prop { get; set; }" =? None

    [<Test>]
    let ``fault effect for signature incompatible port is valid`` () =
        getDiagnostic "public void Void2Void(int i) { }" =? signatureIncompatible 12 "Void2Void" "X.F.Void2Void(int)" "X.Void2Void()"
        getDiagnostic "public int Void2Void() { return 0; }" =? signatureIncompatible 11 "Void2Void" "X.F.Void2Void()" "X.Void2Void()"
        getDiagnostic "public int Int2Int(bool a) { return 1; }" =? signatureIncompatible 11 "Int2Int" "X.F.Int2Int(bool)" "X.Int2Int(int)"
        getDiagnostic "public bool Int2Int(int a) { return false; }" =? signatureIncompatible 12 "Int2Int" "X.F.Int2Int(int)" "X.Int2Int(int)"
        getDiagnostic "public void Int2Int() { }" =? signatureIncompatible 12 "Int2Int" "X.F.Int2Int()" "X.Int2Int(int)"
        getDiagnostic "public bool Overloaded() { return false; }" =? signatureIncompatible 12 "Overloaded" "X.F.Overloaded()" "X.Overloaded(int)"
        getDiagnostic "public void Ref(out int q) { q = 0; }" =? signatureIncompatible 12 "Ref" "X.F.Ref(out int)" "X.Ref(ref int)"
        getDiagnostic "public void Out(ref int q) { q = 1; }" =? signatureIncompatible 12 "Out" "X.F.Out(ref int)" "X.Out(out int)"
        getDiagnostic "public void Ref(int q) { q = 0; }" =? signatureIncompatible 12 "Ref" "X.F.Ref(int)" "X.Ref(ref int)"
        getDiagnostic "public void Out(int q) { q = 1; }" =? signatureIncompatible 12 "Out" "X.F.Out(int)" "X.Out(out int)"

    [<Test>]
    let ``fault effect for property with different type is invalid`` () =
        getDiagnostic "public bool GetProp => false;" =? propertyType 12 "GetProp" "X.F.GetProp" "int"
        getDiagnostic "public bool SetProp { set { } }" =? propertyType 12 "SetProp" "X.F.SetProp" "int"
        getDiagnostic "public bool Prop { get; set; }" =? propertyType 12 "Prop" "X.F.Prop" "int"

    [<Test>]
    let ``fault effect overriding port with optional parameter is valid if it has no optional parameter`` () =
        getDiagnostic "public void Optional(int g) { }" =? None

    [<Test>]
    let ``fault effect with optional parameter is invalid`` () =
        getDiagnostic "public void Optional(int g = 4) { }" =? optionalParameter 25 "X.F.Optional(int)" "g"
        getDiagnostic "public int Int2Int(int x = 2) { return x; }" =? optionalParameter 23 "X.F.Int2Int(int)" "x"

    [<Test>]
    let ``fault effect with generic parameter of generic component is valid`` () =
        TestCompilation.GetDiagnostic (FaultEffectAnalyzer ()) "class X<T> : Component { public T M(T t) { return t; } [Transient] class F : Fault { public T M(T t) { return t; } }}" =? None

    [<Test>]
    let ``fault effect overriding accessible base member is invalid`` () =
        getDiagnostic "public void Inherited() { }" =? baseMember 12 "Inherited" "X.F.Inherited()" "Y.Inherited()"
        getDiagnostic "public int InheritedProp => 1;" =? baseMember 11 "InheritedProp" "X.F.InheritedProp" "Y.InheritedProp"

    [<Test>]
    let ``fault effect overriding inaccessible base member is invalid`` () =
        getDiagnostic "public void Inaccessible() { }" =? unknownMethodPort 12 "Inaccessible" "X.F.Inaccessible()"
        getDiagnostic "public int InaccessibleProp => 1;" =? unknownPropertyPort 11 "InaccessibleProp" "X.F.InaccessibleProp"

    [<Test>]
    let ``fault effect property that overrides method is invalid`` () =
        getDiagnostic "public int GetMethodProp => 1;" =? unknownPropertyPort 11 "GetMethodProp" "X.F.GetMethodProp"
        getDiagnostic "public int SetMethodProp { set {} }" =? unknownPropertyPort 11 "SetMethodProp" "X.F.SetMethodProp"

    [<Test>]
    let ``fault effect method that overrides property is invalid`` () =
        getDiagnostic "public int GetProp() => 1;" =? unknownMethodPort 11 "GetProp" "X.F.GetProp()" 
        getDiagnostic "public void SetProp(int value) {}" =? unknownMethodPort 12 "SetProp" "X.F.SetProp(int)" 

    [<Test>]
    let ``overriding get-only property with get-set fault effect is invalid`` () =
        getDiagnostic "public int GetProp { get; set; }" =? unknownPropertyPort 11 "GetProp" "X.F.GetProp"

    [<Test>]
    let ``overriding set-only property with get-set fault effect is invalid`` () =
        getDiagnostic "public int SetProp { get; set; }" =? unknownPropertyPort 11 "SetProp" "X.F.SetProp"

    [<Test>]
    let ``overriding get-set property with get-only fault effect is valid`` () =
        getDiagnostic "public int Prop => 1;" =? None

    [<Test>]
    let ``overriding get-set property with set-only fault effect`` () =
        getDiagnostic "public int Prop { set {} }" =? None