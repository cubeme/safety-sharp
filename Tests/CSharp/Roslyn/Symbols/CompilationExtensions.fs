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

namespace Roslyn.Symbols.CompilationExtensions

open System
open System.Linq
open NUnit.Framework
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp.Roslyn.Symbols
open SafetySharp.Modeling

[<TestFixture>]
module ``GetTypeSymbol methods`` =
    [<Test>]
    let ``throws when compilation is null`` () =
        raisesArgumentNullException "compilation" (fun () -> (null : Compilation).GetTypeSymbol<obj> () |> ignore)
        raisesArgumentNullException "compilation" (fun () -> (null : Compilation).GetTypeSymbol (typeof<obj>) |> ignore)
        raisesArgumentNullException "compilation" (fun () -> (null : Compilation).GetTypeSymbol (typeof<obj>.FullName) |> ignore)

    [<Test>]
    let ``throws when type is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "type" (fun () -> compilation.CSharpCompilation.GetTypeSymbol (null : Type) |> ignore)

    [<Test>]
    let ``throws when metadataName is null`` () =
        let compilation = TestCompilation ""
        raisesArgumentNullException "metadataName" (fun () -> compilation.CSharpCompilation.GetTypeSymbol (null : string) |> ignore)

    [<Test>]
    let ``throws when metadataName is empty`` () =
        let compilation = TestCompilation ""
        raisesArgumentException "metadataName" (fun () -> compilation.CSharpCompilation.GetTypeSymbol " " |> ignore)

    [<Test>]
    let ``returns the Component class symbol`` () =
        let compilation = TestCompilation ""
        compilation.CSharpCompilation.GetTypeSymbol<Component>().Name =? typeof<Component>.Name
        compilation.CSharpCompilation.GetTypeSymbol(typeof<Component>).Name =? typeof<Component>.Name
        compilation.CSharpCompilation.GetTypeSymbol(typeof<Component>.FullName).Name =? typeof<Component>.Name

[<TestFixture>]
module ``GetComponentClassSymbol method`` =
    [<Test>]
    let ``throws when compilation is null`` () =
        raisesArgumentNullException "compilation" (fun () -> (null : Compilation).GetComponentClassSymbol () |> ignore)

    [<Test>]
    let ``returns the Component class symbol`` () =
        let compilation = TestCompilation ""
        compilation.CSharpCompilation.GetComponentClassSymbol().Name =? typeof<Component>.Name

[<TestFixture>]
module ``GetComponentInterfaceSymbol method`` =
    [<Test>]
    let ``throws when compilation is null`` () =
        raisesArgumentNullException "compilation" (fun () -> (null : Compilation).GetComponentInterfaceSymbol () |> ignore)

    [<Test>]
    let ``returns the IComponent interface symbol`` () =
        let compilation = TestCompilation ""
        compilation.CSharpCompilation.GetComponentInterfaceSymbol().Name =? typeof<IComponent>.Name

[<TestFixture>]
module ``GetUpdateMethodSymbol method`` =
    [<Test>]
    let ``throws when compilation is null`` () =
        raisesArgumentNullException "compilation" (fun () -> (null : Compilation).GetUpdateMethodSymbol () |> ignore)

    [<Test>]
    let ``returns the BehaviorAttribute symbol`` () =
        let compilation = TestCompilation ""
        compilation.CSharpCompilation.GetUpdateMethodSymbol().Name =? "Update"
