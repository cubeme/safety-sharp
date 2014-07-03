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

namespace SafetySharp.Internal.CSharp.Normalization

open System
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.Internal.CSharp.Roslyn
open SafetySharp.Modeling

/// Replaces all extern method declarations within a component with a property of the appropriate System.Func<> or System.Action<> type.
/// For instance:
/// - public extern void MyMethod(int a, decimal b) 
///     --> public Action<int, decimal> MyMethod { private get; set; }
/// - private extern bool MyMethod(int a)
///     --> private Func<int, bool> MyMethod { private get; set; }
type internal ComponentExternMethodNormalizer () =
    inherit CSharpNormalizer (NormalizationScope.Components)

    override this.VisitMethodDeclaration node =
        if node.Modifiers.Any SyntaxKind.ExternKeyword then
            let propertyType = node.GetDelegateType this.semanticModel
            let getterVisibility = if node.Visibility = Visibility.Private then None else Some Private
            let property = Syntax.AutoProperty node.Identifier.ValueText propertyType node.Visibility getterVisibility None
            
            let property =
                if node.ExplicitInterfaceSpecifier <> null then
                    let property = property.WithExplicitInterfaceSpecifier node.ExplicitInterfaceSpecifier
                    property.WithModifiers (SyntaxTokenList ())
                else
                    property

            let property = 
                if node.AttributeLists.Count <> 0 then
                    property.WithAttributeLists(node.AttributeLists)
                else
                    property

            upcast (property
                |> Syntax.AsSingleLine
                |> Syntax.WithTriviaFromNode node
                |> Syntax.EnsureSameLineCount node)
        else
            upcast node

/// Replaces all required port method declarations within a component interface with a property of the appropriate 
//// System.Func<> or System.Action<> type.
/// For instance: 
/// - extern void MyMethod(int a, decimal b) 
///     --> Action<int, decimal> MyMethod { set; }
/// - extern bool MyMethod(int a)
///     --> Func<int, bool> MyMethod { set; }
type internal InterfaceRequiredPortNormalizer () =
    inherit CSharpNormalizer (NormalizationScope.ComponentInterfaces)

    override this.VisitMethodDeclaration node =
        if node.HasAttribute<RequiredAttribute> this.semanticModel then
            let propertyType = node.GetDelegateType this.semanticModel
            let getterVisibility = if node.Visibility = Visibility.Private then None else Some Private
            let property = Syntax.InterfaceProperty node.Identifier.ValueText propertyType false true
            
            let property = 
                if node.AttributeLists.Count <> 0 then
                    property.WithAttributeLists(node.AttributeLists)
                else
                    property

            upcast (property
                |> Syntax.AsSingleLine
                |> Syntax.WithTriviaFromNode node
                |> Syntax.EnsureSameLineCount node)
        else
            upcast node