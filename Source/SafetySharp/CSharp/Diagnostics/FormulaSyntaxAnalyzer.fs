﻿// The MIT License (MIT)
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

/// Checks for unsupported C# features within a formula expression.
type internal FormulaSyntaxAnalyzerVisitor (emitDiagnostic) =
    inherit CSharpSyntaxWalker ()

    /// Visits the descendant nodes of <paramref name="node" />.
    member private this.VisitDescendantNodes (node : SyntaxNode) =
        base.DefaultVisit node

    /// Reports the node as a use of an unsupported C# feature.
    override this.DefaultVisit node                 = node.CSharpKind().ToDescription () |> emitDiagnostic node

    (* Supported C# syntax elements *)
    override this.VisitIdentifierName node          = this.VisitDescendantNodes node
    override this.VisitQualifiedName node           = this.VisitDescendantNodes node
    override this.VisitLiteralExpression node       = this.VisitDescendantNodes node
    override this.VisitMemberAccessExpression node  = this.VisitDescendantNodes node
    override this.VisitParenthesizedExpression node = this.VisitDescendantNodes node

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
        | SyntaxKind.GreaterThanOrEqualExpression -> this.VisitDescendantNodes node
        | _ -> node.CSharpKind().ToDescription () |> emitDiagnostic node

    override this.VisitPrefixUnaryExpression node = 
        match node.CSharpKind () with
        | SyntaxKind.UnaryMinusExpression
        | SyntaxKind.UnaryPlusExpression
        | SyntaxKind.LogicalNotExpression -> this.VisitDescendantNodes node
        | _ -> node.CSharpKind().ToDescription () |> emitDiagnostic node

/// Ensures that no enumeration members explicitly declare a constant value.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.IllegalCSharpSyntaxElementInFormula, LanguageNames.CSharp)>]
type FormulaSyntaxAnalyzer () as this =
    inherit SemanticModelAnalyzer ()

    do this.Error DiagnosticIdentifiers.IllegalCSharpSyntaxElementInFormula
        "A formula uses an unsupported C# syntax element."
        "State formula uses unsupported C# feature: '{0}'."

    override this.Analyze semanticModel addDiagnostic cancellationToken =
        let emitDiagnostic (node : SyntaxNode) (description : string) = 
            addDiagnostic.Invoke (node, description)

        let formulaVisitor = FormulaSyntaxAnalyzerVisitor emitDiagnostic
        let expressionType = typeof<Expression<obj>>.GetGenericTypeDefinition ()
        let funcType = typeof<Func<obj>>.GetGenericTypeDefinition ()
        let booleanSymbol = semanticModel.GetTypeSymbol<bool> ()
        let expressionSymbol = semanticModel.GetTypeSymbol expressionType
        let funcSymbol = semanticModel.GetTypeSymbol funcType
        let funcSymbol = funcSymbol.Construct booleanSymbol
        let expressionSymbol = expressionSymbol.Construct funcSymbol

        semanticModel.SyntaxTree.Descendants<InvocationExpressionSyntax>()
        |> Seq.where (fun invocation -> invocation.IsFormulaFunction semanticModel)
        |> Seq.collect (fun invocation -> invocation.ArgumentList.Arguments)
        |> Seq.where (fun argument -> argument.IsOfType (semanticModel, booleanSymbol) || argument.IsOfType (semanticModel, expressionSymbol))
        |> Seq.map (fun argument -> argument.Expression)
        |> Seq.iter formulaVisitor.Visit