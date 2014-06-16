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

/// Checks for unsupported C# features within a component declaration.
type internal ComponentSyntaxAnalyzerVisitor (emitDiagnostic) =
    inherit CSharpSyntaxWalker ()

    /// Visits the descendant nodes of <paramref name="node" />.
    member private this.VisitDescendantNodes (node : SyntaxNode) =
        base.DefaultVisit node

    /// Reports the node as a use of an unsupported C# feature.
    override this.DefaultVisit node                 = node.CSharpKind().ToDescription () |> emitDiagnostic node

    /// Does nothing, as constructors support all C# features.
    override this.VisitConstructorDeclaration node  = () 

    (* Supported C# syntax elements *)
    override this.VisitClassDeclaration node        = this.VisitDescendantNodes node
    override this.VisitIdentifierName node          = this.VisitDescendantNodes node
    override this.VisitQualifiedName node           = this.VisitDescendantNodes node
    override this.VisitAliasQualifiedName node      = this.VisitDescendantNodes node
    override this.VisitExternAliasDirective node    = this.VisitDescendantNodes node
    override this.VisitFieldDeclaration node        = this.VisitDescendantNodes node
    override this.VisitBaseList node                = this.VisitDescendantNodes node
    override this.VisitMethodDeclaration node       = this.VisitDescendantNodes node
    override this.VisitVariableDeclaration node     = this.VisitDescendantNodes node
    override this.VisitVariableDeclarator node      = this.VisitDescendantNodes node
    override this.VisitPredefinedType node          = this.VisitDescendantNodes node
    override this.VisitBlock node                   = this.VisitDescendantNodes node
    override this.VisitParameterList node           = this.VisitDescendantNodes node
    override this.VisitReturnStatement node         = this.VisitDescendantNodes node
    override this.VisitExpressionStatement node     = this.VisitDescendantNodes node
    override this.VisitInvocationExpression node    = this.VisitDescendantNodes node
    override this.VisitBinaryExpression node        = this.VisitDescendantNodes node
    override this.VisitPrefixUnaryExpression node   = this.VisitDescendantNodes node
    override this.VisitPostfixUnaryExpression node  = this.VisitDescendantNodes node
    override this.VisitArgumentList node            = this.VisitDescendantNodes node
    override this.VisitArgument node                = this.VisitDescendantNodes node
    override this.VisitLiteralExpression node       = this.VisitDescendantNodes node
    override this.VisitEqualsValueClause node       = this.VisitDescendantNodes node
    override this.VisitMemberAccessExpression node  = this.VisitDescendantNodes node

/// Ensures that no enumeration members explicitly declare a constant value.
[<DiagnosticAnalyzer>]
[<ExportDiagnosticAnalyzer(DiagnosticIdentifiers.IllegalCSharpSyntaxElementInComponent, LanguageNames.CSharp)>]
type ComponentSyntaxAnalyzer () as this =
    inherit SemanticModelAnalyzer ()

    do this.Error DiagnosticIdentifiers.IllegalCSharpSyntaxElementInComponent
        "A model component uses an unsupported C# syntax element."
        "C# feature is unsupported: {0}"

    override this.Analyze semanticModel addDiagnostic cancellationToken =
        let emitDiagnostic (node : SyntaxNode) (description : string) = 
            addDiagnostic.Invoke (node, description)

        let componentVisitor = ComponentSyntaxAnalyzerVisitor emitDiagnostic

        semanticModel.SyntaxTree.Descendants<ClassDeclarationSyntax>()
        |> Seq.where (fun classDeclaration -> classDeclaration.IsComponentDeclaration semanticModel)
        |> Seq.iter componentVisitor.Visit