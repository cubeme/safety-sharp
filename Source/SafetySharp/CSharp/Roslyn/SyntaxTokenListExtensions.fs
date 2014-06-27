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

namespace SafetySharp.CSharp.Roslyn

open System
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

/// Provides extension methods for working with <see cref="SyntaxTokenList" /> instances.
[<AutoOpen>]
module SyntaxTokenListExtensions =
    type SyntaxTokenList with

        /// Deduces the type or member visibility from the syntax token list.
        member this.GetVisibility defaultVisibility =
            let isPrivate = this |> Seq.exists (fun modifier -> modifier.CSharpKind () = SyntaxKind.PrivateKeyword)
            let isProtected = this |> Seq.exists (fun modifier -> modifier.CSharpKind () = SyntaxKind.ProtectedKeyword)
            let isInternal = this |> Seq.exists (fun modifier -> modifier.CSharpKind () = SyntaxKind.InternalKeyword)
            let isPublic = this |> Seq.exists (fun modifier -> modifier.CSharpKind () = SyntaxKind.PublicKeyword)

            if not isPrivate && not isProtected && not isInternal && not isPublic then
                defaultVisibility
            elif isPrivate && not isProtected && not isInternal && not isPublic then
                Private
            elif isProtected && not isPrivate && not isInternal && not isPublic then
                Protected
            elif isInternal && not isPrivate && not isProtected && not isPublic then
                Internal
            elif isProtected && isInternal && not isPrivate && not isPublic then
                ProtectedInternal
            elif isPublic && not isPrivate && not isProtected && not isInternal then
                Public
            else
                invalidOp "Unable to determine visibility."