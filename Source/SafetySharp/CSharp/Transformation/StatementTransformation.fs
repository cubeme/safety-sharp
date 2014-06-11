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

namespace SafetySharp.CSharp

open System.Collections.Immutable

open SafetySharp.Metamodel
open SafetySharp.CSharp.Roslyn

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

module internal StatementTransformation =

    /// Transforms C# statements to metamodel statements.
    let Transform (symbolMap : SymbolMap) (semanticModel : SemanticModel) (statement : StatementSyntax) =
        let transformExpression = ExpressionTransformation.Transform symbolMap semanticModel
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
            GuardedCommandStatement [ (condition, ifStatement) ]

        | IfStatement (condition, ifStatement, Some elseStatement) ->
            let ifCondition = transformExpression condition
            let ifStatement = transform ifStatement
            let elseCondition = UnaryExpression (ifCondition, UnaryOperator.LogicalNot)
            let elseStatement = transform elseStatement
            GuardedCommandStatement [ (ifCondition, ifStatement); (elseCondition, elseStatement) ]

        | ExpressionStatement expression ->
            match expression with
            | AssignmentExpression (left, right) ->
                AssignmentStatement (transformExpression left, transformExpression right)
            | _ -> statement.CSharpKind () |> sprintf "Encountered an unexpected C# syntax node: '%A'." |> invalidOp

        | _ ->
            statement.CSharpKind () |> sprintf "Encountered an unexpected C# syntax node: '%A'." |> invalidOp

        transform statement