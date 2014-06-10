namespace SafetySharp.CSharp

open SafetySharp.Metamodel
open SafetySharp.CSharp.Roslyn

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

module Transformation =
    let TransformExpression = function
        | LiteralExpression (kind, value) ->
            match kind with
            | SyntaxKind.TrueKeyword -> BooleanLiteral true
            | SyntaxKind.FalseKeyword -> BooleanLiteral false
            | SyntaxKind.NumericLiteralToken ->
                match value with
                | :? int as value -> IntegerLiteral value
                | :? decimal as value -> DecimalLiteral value
                | _ ->
                    invalidOp <| sprintf "Numeric literals of type '%A' are not supported." kind
            | _ ->
                invalidOp <| sprintf "Unsupported C# literal: '%A'" kind
        | _ ->
            failwith "TODO"
        