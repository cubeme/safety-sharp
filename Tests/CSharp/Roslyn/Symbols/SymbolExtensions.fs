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

namespace Roslyn.Symbols.SymbolExtensions

open System
open System.Linq
open System.Diagnostics
open System.Runtime.CompilerServices
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharpCompiler.Roslyn.Symbols
open SafetySharp.Modeling

[<TestFixture>]
module ``HasAttribute methods`` =
    let fieldHasAttribute<'T when 'T :> Attribute> csharpCode =
        let compilation = TestCompilation csharpCode
        let fieldSymbol = compilation.FindFieldSymbol "C" "f"
        fieldSymbol.HasAttribute<'T> compilation.CSharpCompilation && fieldSymbol.HasAttribute<'T> compilation.SemanticModel

    let propertyHasAttribute<'T when 'T :> Attribute> csharpCode =
        let compilation = TestCompilation csharpCode
        let propertySymbol = compilation.FindPropertySymbol "C" "P"
        propertySymbol.HasAttribute<'T> compilation.CSharpCompilation && propertySymbol.HasAttribute<'T> compilation.SemanticModel

    let methodHasAttribute<'T when 'T :> Attribute> csharpCode =
        let compilation = TestCompilation csharpCode
        let methodSymbol = compilation.FindMethodSymbol "C" "M"
        methodSymbol.HasAttribute<'T> compilation.CSharpCompilation && methodSymbol.HasAttribute<'T> compilation.SemanticModel

    let classHasAttribute<'T when 'T :> Attribute> csharpCode =
        let compilation = TestCompilation csharpCode
        let classSymbol = compilation.FindClassSymbol "C"
        classSymbol.HasAttribute<'T> compilation.CSharpCompilation && classSymbol.HasAttribute<'T> compilation.SemanticModel

    let interfaceHasAttribute<'T when 'T :> Attribute> csharpCode =
        let compilation = TestCompilation csharpCode
        let interfaceSymbol = compilation.FindInterfaceSymbol "I"
        interfaceSymbol.HasAttribute<'T> compilation.CSharpCompilation && interfaceSymbol.HasAttribute<'T> compilation.SemanticModel

    [<Test>]
    let ``throws when symbol is null`` () =
        let compilation = TestCompilation ""
        let symbol = compilation.CSharpCompilation.GetTypeSymbol<ProvidedAttribute> ()
        raisesArgumentNullException "symbol" (fun () -> (null : ISymbol).HasAttribute symbol |> ignore)
        raisesArgumentNullException "symbol" (fun () -> (null : ISymbol).HasAttribute<ProvidedAttribute> compilation.CSharpCompilation |> ignore)
        raisesArgumentNullException "symbol" (fun () -> (null : ISymbol).HasAttribute<ProvidedAttribute> compilation.SemanticModel |> ignore)

    [<Test>]
    let ``throws when compilation is null`` () =
        let compilation = TestCompilation "class C {}"
        let symbol = compilation.FindClassSymbol "C"
        raisesArgumentNullException "compilation" (fun () -> symbol.HasAttribute<ProvidedAttribute> (null : Compilation) |> ignore)

    [<Test>]
    let ``throws when semantic model is null`` () =
        let compilation = TestCompilation "class C {}"
        let symbol = compilation.FindClassSymbol "C"
        raisesArgumentNullException "semanticModel" (fun () -> symbol.HasAttribute<ProvidedAttribute> (null : SemanticModel) |> ignore)

    [<Test>]
    let ``returns false if property has no attribute`` () =
        propertyHasAttribute<ProvidedAttribute> "class C { int P { get; set; }}" =? false

    [<Test>]
    let ``returns false if property has different attribute`` () =
        propertyHasAttribute<ProvidedAttribute> "class C { [Required] int P { get; set; }}" =? false

    [<Test>]
    let ``returns true if property has attribute`` () =
        propertyHasAttribute<ProvidedAttribute> "class C { [Provided] int P { get; set; }}" =? true

    [<Test>]
    let ``returns false if method has no attribute`` () =
        methodHasAttribute<ProvidedAttribute> "class C { void M() {}}" =? false

    [<Test>]
    let ``returns false if method has different attribute`` () =
        methodHasAttribute<ProvidedAttribute> "class C { [Required] void M() {}}" =? false

    [<Test>]
    let ``returns true if method has attribute`` () =
        methodHasAttribute<ProvidedAttribute> "class C { [Provided] void M() {}}" =? true

    [<Test>]
    let ``returns false if field has no attribute`` () =
        fieldHasAttribute<ProvidedAttribute> "class C { int f; }" =? false

    [<Test>]
    let ``returns false if field has different attribute`` () =
        fieldHasAttribute<ProvidedAttribute> "class C { [System.Runtime.CompilerServices.CompilerGenerated] int f; }" =? false

    [<Test>]
    let ``returns true if field has attribute`` () =
        fieldHasAttribute<System.Runtime.CompilerServices.CompilerGeneratedAttribute> 
            "class C { [System.Runtime.CompilerServices.CompilerGenerated] int f; }" =? true

    [<Test>]
    let ``returns false if class has no attribute`` () =
        classHasAttribute<CompilerGeneratedAttribute> "class C { }" =? false

    [<Test>]
    let ``returns false if class has different attribute`` () =
        classHasAttribute<CompilerGeneratedAttribute> "[System.SerializableAttribute] class C { }" =? false

    [<Test>]
    let ``returns true if class has attribute`` () =
        classHasAttribute<CompilerGeneratedAttribute> "[System.Runtime.CompilerServices.CompilerGenerated] class C { }" =? true

    [<Test>]
    let ``returns false if interface has no attribute`` () =
        interfaceHasAttribute<CompilerGeneratedAttribute> "interface I { }" =? false

    [<Test>]
    let ``returns false if interface has different attribute`` () =
        interfaceHasAttribute<CompilerGeneratedAttribute> "class X : System.Attribute {} [X] interface I { }" =? false

    [<Test>]
    let ``returns true if interface has attribute`` () =
        interfaceHasAttribute<CompilerGeneratedAttribute> "[System.Runtime.CompilerServices.CompilerGenerated] interface I { }" =? true