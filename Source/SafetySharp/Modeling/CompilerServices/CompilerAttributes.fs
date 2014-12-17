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

namespace SafetySharp.Modeling.CompilerServices

open System
open SafetySharp

/// When applied to a method parameter, instructs the SafetySharp compiler to lift an expression 'expr'
/// to a lambda function of the form '() => expr'.
[<AttributeUsage(AttributeTargets.Parameter, AllowMultiple = true, Inherited = false)>]
[<Sealed>]
type LiftExpressionAttribute () =
    inherit Attribute ()

///// Provides metadata about a compilation unit within a SafetySharp modeling assembly.
//[<AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true, Inherited = false)>]
//[<Sealed>]
//type ModelingCompilationUnitAttribute (syntaxTree : string, filePath : string) =
//    inherit Attribute ()
//
//    /// Gets the syntax tree of the compilation unit.
//    member this.SyntaxTree = 
//        nullOrWhitespaceArg syntaxTree "syntaxTree"
//        nullOrWhitespaceArg filePath "filePath"
//        SyntaxFactory.ParseSyntaxTree (syntaxTree, filePath)
//
///// Provides metadata about a SafetySharp modeling assembly.
//[<AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true, Inherited = false)>]
//[<AllowNullLiteral; Sealed>]
//type ModelingAssemblyAttribute (compilerVersion : string) =
//    inherit Attribute ()
//
//    /// Gets the version string of the SafetySharp compiler that was used to compile the modeling assembly.
//    member this.CompilerVersion = 
//        nullOrWhitespaceArg compilerVersion "compilerVersion"
//        compilerVersion