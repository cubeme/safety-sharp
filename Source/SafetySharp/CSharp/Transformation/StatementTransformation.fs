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

namespace SafetySharp.CSharp.Transformation

open System.Collections.Immutable
open SafetySharp.Metamodel
open SafetySharp.Utilities
open SafetySharp.CSharp.Roslyn
open SafetySharp.CSharp.Extensions
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

module internal StatementTransformation =

    /// Transforms C# statements to metamodel statements.
    let Transform (symbolResolver : SymbolResolver) (semanticModel : SemanticModel) (statement : StatementSyntax) =
        let transformExpression = ExpressionTransformation.Transform symbolResolver semanticModel
        let rec transform = function
        | EmptyStatement ->
            EmptyStatement

        | BlockStatement statements ->
            statements |> Seq.map transform |> List.ofSeq |> BlockStatement 

        | ReturnStatement None ->
            ReturnStatement None

        | ReturnStatement (Some expression) ->
            transformExpression expression |> Some |> ReturnStatement

        | IfStatement (condition, ifStatement, None) ->
            let condition = transformExpression condition
            let ifStatement = transform ifStatement
            GuardedCommandStatement [(condition, ifStatement)]

        | IfStatement (condition, ifStatement, Some elseStatement) ->
            let ifCondition = transformExpression condition
            let ifStatement = transform ifStatement
            let elseCondition = UnaryExpression (ifCondition, UnaryOperator.LogicalNot)
            let elseStatement = transform elseStatement
            GuardedCommandStatement [(ifCondition, ifStatement); (elseCondition, elseStatement)]

        | ExpressionStatement expression ->

            match expression with
            | AssignmentExpression (left, right) ->
                AssignmentStatement (transformExpression left, transformExpression right)

            | InvocationExpression invocation ->
                let methodSymbol = semanticModel.GetSymbol<IMethodSymbol> invocation
                let arguments = invocation.ArgumentList.Arguments
                   
                let chooseBooleanValueMethodSymbol = semanticModel.GetChooseBooleanMethodSymbol true
                let chooseIntegerValueMethodSymbol = semanticModel.GetChooseValueMethodSymbol true SpecialType.System_Int32
                let chooseDecimalValueMethodSymbol = semanticModel.GetChooseValueMethodSymbol true SpecialType.System_Decimal

                if chooseBooleanValueMethodSymbol.Equals methodSymbol then
                    let assignmentTarget = transformExpression arguments.[0].Expression
                    GuardedCommandStatement [
                        (BooleanLiteral true, AssignmentStatement (assignmentTarget, BooleanLiteral true))
                        (BooleanLiteral true, AssignmentStatement (assignmentTarget, BooleanLiteral false))
                    ]

                elif chooseDecimalValueMethodSymbol.Equals methodSymbol || chooseIntegerValueMethodSymbol.Equals methodSymbol then
                    let assignmentTarget = transformExpression arguments.[0].Expression
                    let expressions = arguments |> Seq.skip 1 |> Seq.map (fun argument -> transformExpression argument.Expression)
                    let statements = expressions |> Seq.map (fun expression -> AssignmentStatement(assignmentTarget, expression))
                    let clauses = statements |> Seq.map (fun statement -> (BooleanLiteral true, statement))
                    clauses |> List.ofSeq |> GuardedCommandStatement
                else
                    invalidOp "Unsupported C# Choose call: '%A'." invocation

            | _ -> invalidOp "Encountered an unexpected C# syntax node: '%A'." <| statement.CSharpKind ()

        | _ ->
             invalidOp "Encountered an unexpected C# syntax node: '%A'." <| statement.CSharpKind ()

        transform statement

    /// Transforms the body of the given method symbol.
    let private transformMethodBody (compilation : Compilation) (symbolResolver : SymbolResolver) methodSymbol =
        let csharpMethod = symbolResolver.ResolveCSharpMethod methodSymbol

        // Special case: We're trying to transform the Update method of a component that didn't override it
        // and none of its parents did. In that case, the resolver returns the symbol for Component.Update, for
        // which we don't have the source. Just return an empty statement in that case.
        if csharpMethod.Equals (compilation.GetUpdateMethodSymbol ()) then
            EmptyStatement
        else
            let syntaxReference = csharpMethod.DeclaringSyntaxReferences.[0]
            let methodDeclaration = syntaxReference.GetSyntax() :?> MethodDeclarationSyntax
            let semanticModel = compilation.GetSemanticModel syntaxReference.SyntaxTree

            Transform symbolResolver semanticModel methodDeclaration.Body

    /// Transforms the bodies of all of the component's methods.
    let private transformComponentMethods compilation symbolResolver componentSymbol =
        componentSymbol.UpdateMethod :: componentSymbol.Methods
        |> Seq.map (fun methodSymbol -> ((componentSymbol, methodSymbol), transformMethodBody compilation symbolResolver methodSymbol))

    /// Transforms the bodies of all methods declared by the components in the symbol resolver.
    let TransformMethodBodies (compilation : Compilation) (symbolResolver : SymbolResolver) =
        symbolResolver.ModelSymbol.ComponentSymbols 
        |> Seq.collect (transformComponentMethods compilation symbolResolver)
        |> Map.ofSeq