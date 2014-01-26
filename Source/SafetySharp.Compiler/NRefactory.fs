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

module internal SafetySharp.Compiler.NRefactory

open System
open System.Diagnostics
open System.Linq

open ICSharpCode.NRefactory
open ICSharpCode.NRefactory.CSharp
open ICSharpCode.NRefactory.CSharp.Resolver
open ICSharpCode.NRefactory.Semantics
open ICSharpCode.NRefactory.TypeSystem

// ======================================================================================================================================
// Compilation Context
// ======================================================================================================================================

/// Provides access to all NRefactory instances required to compile the C# code.
type CompilationContext = {
    /// The syntax tree of the C# file that is being compiled.
    SyntaxTree : SyntaxTree

    /// The resolver that should be used to resolve all semantic information of the file that is being compiled.
    Resolver : CSharpAstResolver
} 

// ======================================================================================================================================
// Syntactic Helpers
// ======================================================================================================================================

/// Gets all descendants of the given type from the NRefactory AstNode (including the AstNode itself).
let getDescendantsAndSelf<'a> (node : AstNode) =
    node.DescendantsAndSelf.OfType<'a>()

/// Gets all descendants of the given type from the NRefactory AstNode.
let getDescendants<'a> (node : AstNode) =
    node.Descendants.OfType<'a>()

// ======================================================================================================================================
// Semantic Analysis Helpers
// ======================================================================================================================================

/// Resolves the semantic information for the given NRefactory AstNode, throwing an exception if the resolve process failed
/// or if the resolve result has an unexpected type.
let private resolve<'a when 'a :> ResolveResult> context (node : AstNode) =
    match context.Resolver.Resolve node with
    | :? 'a as result 
        -> result
    | :? ErrorResolveResult as error 
        -> failwithf "Resolve operation failed: '%s'." error.Message
    | result 
        -> failwithf "Unexpected resolve result: '%s'." (result.GetType().FullName)  

/// Resolves the type of the given NRefactory TypeDeclaration.
let resolveTypeDeclaration context (typeDeclaration : TypeDeclaration) =
    resolve<TypeResolveResult> context typeDeclaration

/// Resolves the type of the given type reference (i.e., NRefactory AstType).
let resolveTypeReference context (typeReference : AstType) =
    resolve<TypeResolveResult> context typeReference

/// Resolves the value of the NRefactory Expression representing a compile-time constant value.
let resolveCompileTimeConstant<'a> context (expression : Expression) =
    let constant = resolve<ConstantResolveResult> context expression
    Debug.Assert (constant.IsCompileTimeConstant, "Expected a compile time constant value.")

    match constant.ConstantValue with
    | :? 'a as result 
        -> result
    | null 
        -> failwith "Encountered unexpected NULL value."
    | _ 
        -> failwithf "Unexpected type of constant value: '%s'." (constant.ConstantValue.GetType().FullName)

/// Resolves the namespace of the given NRefactory TypeDeclaration.
let resolveNamespace context (typeDeclaration : TypeDeclaration) =
    let resolveResult = resolveTypeDeclaration context typeDeclaration
    resolveResult.Type.Namespace