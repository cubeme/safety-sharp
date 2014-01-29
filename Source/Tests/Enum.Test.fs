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

module SafetySharp.Compiler.Tests.Enum

open NUnit.Framework
open FsUnit

open SafetySharp.Compiler
open SafetySharp.Compiler.Model

open ICSharpCode.NRefactory
open ICSharpCode.NRefactory.CSharp
open ICSharpCode.NRefactory.CSharp.Resolver
open ICSharpCode.NRefactory.Semantics
open ICSharpCode.NRefactory.TypeSystem

/// Parses the given enum declaration string and invokes the given action for the compilation context returned
/// by NRefactory.
let private act declaration action =
    let context = NRefactory.ParseString declaration

    let enumDecl = 
        NRefactory.getDescendantsAndSelf<TypeDeclaration> context.SyntaxTree
        |> Seq.head 

    action context enumDecl

/// Parses the given enum declaration string and returns the validation result.
let validate declaration =
    act declaration CSharpValidator.validateEnumDeclaration

/// Parses the given enum declaration string and returns the model enum declaration.
let create declaration =
    act declaration CSharpParser.createEnumDeclaration

/// Returns a list of the names of all members of the declared enum.
let memberNames declaration =
    declaration.Members |> Seq.map (fun m -> m.Name)

[<Test>]
let ``enum with implicit underlying type should be valid`` () =
    validate "enum E { A }" |> should be True

[<Test>]
let ``enum with 'int' underlying type should be valid`` () =
    validate "enum E : int { A }" |> should be True

[<Test>]
let ``enum with 'byte' as underlying type should be invalid`` () =
    validate "enum E : byte { A }" |> should be False

[<Test>]
let ``enum with 'sbyte' as underlying type should be invalid`` () =
    validate "enum E : sbyte { A }" |> should be False

[<Test>]
let ``enum with 'short' as underlying type should be invalid`` () =
    validate "enum E : short { A }" |> should be False

[<Test>]
let ``enum with 'ushort' as underlying type should be invalid`` () =
    validate "enum E : ushort { A }" |> should be False

[<Test>]
let ``enum with 'uint' as underlying type should be invalid`` () =
    validate "enum E : uint { A }" |> should be False

[<Test>]
let ``enum with 'long' as underlying type should be invalid`` () =
    validate "enum E : long { A }" |> should be False

[<Test>]
let ``enum with 'ulong' as underlying type should be invalid`` () =
    validate "enum E : ulong { A }" |> should be False

[<Test>]
let ``enum with member expression on first member should be invalid`` () =
    validate "enum E { A = 0, B, C }" |> should be False

[<Test>]
let ``enum with member expression on last member should be invalid`` () =
    validate "enum E { A, B, C = 3 }" |> should be False

[<Test>]
let ``enum name should be 'E'`` () =
    let enum = create "namespace N.N { enum E { } }"
    enum.Name.Name |> should equal "E"

[<Test>]
let ``enum namespace should be 'N.M'`` () =
    let enum = create "namespace N.M { enum E { } }"
    enum.Namespace |> should equal "N.M"

[<Test>]
let ``enum without members should not have any members`` () =
    let enum = create "enum E { }"
    enum.Members |> should equal []

[<Test>]
let ``enum without members should not have one member`` () =
    let enum = create "enum E { X }"
    memberNames enum |> should equal ["X"]

[<Test>]
let ``enum without members should not have three members 'C', 'B', and 'A'`` () =
    let enum = create "enum E { C, B, A }"
    memberNames enum |> should equal ["C"; "B"; "A"]