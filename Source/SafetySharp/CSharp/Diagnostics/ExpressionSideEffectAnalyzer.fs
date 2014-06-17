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

namespace SafetySharp.CSharp.Diagnostics

open System
open System.Collections.Immutable
open System.Linq.Expressions
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Diagnostics
open SafetySharp.Utilities
open SafetySharp.CSharp.Extensions

/// Ensures that an expression is side effect free. TODO: Remove this and normalize later.
type internal ExpressionSideEffectAnalyzerVisitor (emitDiagnostic : DiagnosticCallback) =
    inherit CSharpSyntaxWalker ()

    /// Reports the node as a use of an unsupported C# feature.
    override this.DefaultVisit node                 = emitDiagnostic.Invoke (node, node.CSharpKind().ToDescription ())

    /// Constructors support all C# features, so we don't care about expression with side effects here.
    override this.VisitConstructorDeclaration node  = () 

    (* Supported C# syntax elements *)
    override this.VisitIdentifierName node          = ()
    override this.VisitQualifiedName node           = ()
    override this.VisitLiteralExpression node       = ()
    override this.VisitMemberAccessExpression node  = ()
    override this.VisitParenthesizedExpression node = ()

    // For now, allow method invocations only when the result is immediately assigned to a variable 
    // as well as invocations of void returning methods.
    override this.VisitInvocationExpression node =
        match node.Parent with
        | :? BinaryExpressionSyntax as binaryExpression 
            when binaryExpression.CSharpKind () = SyntaxKind.SimpleAssignmentExpression &&
                 (binaryExpression.Parent :? ExpressionStatementSyntax) ->
            ()
        | :? ExpressionStatementSyntax -> ()
        | _ -> this.DefaultVisit node

    override this.VisitBinaryExpression node = 
        match node.CSharpKind () with
        | SyntaxKind.AddExpression 
        | SyntaxKind.SubtractExpression
        | SyntaxKind.MultiplyExpression
        | SyntaxKind.DivideExpression
        | SyntaxKind.ModuloExpression
        | SyntaxKind.LogicalAndExpression
        | SyntaxKind.LogicalOrExpression
        | SyntaxKind.EqualsExpression
        | SyntaxKind.NotEqualsExpression
        | SyntaxKind.LessThanExpression
        | SyntaxKind.LessThanOrEqualExpression
        | SyntaxKind.GreaterThanExpression
        | SyntaxKind.GreaterThanOrEqualExpression -> ()
        | SyntaxKind.SimpleAssignmentExpression when (node.Parent :? ExpressionStatementSyntax) -> ()
        | _ -> this.DefaultVisit node

    override this.VisitPrefixUnaryExpression node = 
        match node.CSharpKind () with
        | SyntaxKind.UnaryMinusExpression
        | SyntaxKind.UnaryPlusExpression
        | SyntaxKind.LogicalNotExpression -> ()
        | _ -> this.DefaultVisit node

/// Ensures that an expression is side effect free. TODO: Remove this and normalize later.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.IllegalCSharpSyntaxElementInExpression, LanguageNames.CSharp)>]
type ExpressionSideEffectAnalyzer () as this =
    inherit SemanticModelAnalyzer ()

    do this.Error DiagnosticIdentifiers.IllegalCSharpSyntaxElementInExpression
        "For the moment, expressions may not have side effects."
        "For the moment, expressions may not have side effects: Cannot use {0} here as it has (potential) side effects."

    override this.Analyze semanticModel addDiagnostic cancellationToken =
        let formulaVisitor = ExpressionSideEffectAnalyzerVisitor addDiagnostic

        semanticModel.SyntaxTree.Descendants<ClassDeclarationSyntax>()
        |> Seq.where (fun classDeclaration -> classDeclaration.IsComponentDeclaration semanticModel)
        |> Seq.collect (fun classDeclaration -> classDeclaration.Descendants<MethodDeclarationSyntax> ())
        |> Seq.collect (fun methodDeclaration -> methodDeclaration.Body.Descendants<ExpressionSyntax> ())
        |> Seq.iter formulaVisitor.Visit