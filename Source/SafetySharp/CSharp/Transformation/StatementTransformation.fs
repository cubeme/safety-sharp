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

namespace SafetySharp.Internal.CSharp.Transformation
//
//open System.Collections.Immutable
//open SafetySharp.Internal.Metamodel
//open SafetySharp.Internal.Utilities
//open SafetySharp.Internal.CSharp.Roslyn
//open Microsoft.CodeAnalysis
//open Microsoft.CodeAnalysis.CSharp
//open Microsoft.CodeAnalysis.CSharp.Syntax
//
//module internal StatementTransformation =
//
//    /// Transforms an assignment to a field, local, or parameter.
//    let private transformAssignment (symbolResolver : SymbolResolver) (semanticModel : SemanticModel) (target : ExpressionSyntax) expression =
//        let symbolInfo = semanticModel.GetSymbolInfo target
//        match symbolInfo.Symbol with
//        | :? IFieldSymbol as fieldSymbol ->
//            WriteField (symbolResolver.ResolveField fieldSymbol, expression)
//        | :? IParameterSymbol as parameterSymbol ->
//            WriteParameter (symbolResolver.ResolveParameter parameterSymbol, expression)
//        | :? ILocalSymbol as localSymbol ->
//            WriteLocal (symbolResolver.ResolveLocal localSymbol, expression)
//        | null -> invalidOp "Failed to get symbol info for assignment target '%A'." target
//        | _ -> invalidOp "Encountered unexpected symbol '%A' while trying to transform assignment target '%A'." symbolInfo.Symbol target
//
//    /// Transforms C# statements to metamodel statements.
//    let Transform (symbolResolver : SymbolResolver) (semanticModel : SemanticModel) (statement : StatementSyntax) =
//        let transformExpression = 
//            ExpressionTransformation.Transform symbolResolver semanticModel
//
//        let rec transform statement =
//            match statement with
//            | EmptyStatement ->
//                EmptyStatement
//
//            | LocalDeclarationStatement (_, variables) ->
//                variables
//                |> Seq.where (fun variable -> variable.Initializer <> null)
//                |> Seq.map (fun variable ->
//                    let symbol = semanticModel.DeclaredSymbolOf<ILocalSymbol> variable
//                    let localSymbol = symbolResolver.ResolveLocal symbol
//                    WriteLocal (localSymbol, transformExpression variable.Initializer.Value)
//                )
//                |> List.ofSeq
//                |> BlockStatement
//
//            | BlockStatement statements ->
//                statements |> Seq.map transform |> List.ofSeq |> BlockStatement
//
//            | ReturnStatement None ->
//                ReturnStatement None
//
//            | ReturnStatement (Some expression) ->
//                transformExpression expression |> Some |> ReturnStatement
//
//            | IfStatement (condition, ifStatement, None) ->
//                let condition = transformExpression condition
//                let ifStatement = transform ifStatement
//                GuardedCommandStatement [(condition, ifStatement)]
//
//            | IfStatement (condition, ifStatement, Some elseStatement) ->
//                let ifCondition = transformExpression condition
//                let ifStatement = transform ifStatement
//                let elseCondition = UnaryExpression (ifCondition, UnaryOperator.LogicalNot)
//                let elseStatement = transform elseStatement
//                GuardedCommandStatement [(ifCondition, ifStatement); (elseCondition, elseStatement)]
//
//            | ExpressionStatement expression ->
//
//                match expression with
//                | AssignmentExpression (left, right) ->
//                    transformAssignment symbolResolver semanticModel left (transformExpression right)
//
//                | InvocationExpression invocation ->
//                    let methodSymbol = semanticModel.GetReferencedSymbol<IMethodSymbol> invocation
//                    let arguments = invocation.ArgumentList.Arguments
//                   
//                    let chooseBooleanValueMethodSymbol = semanticModel.GetChooseBooleanMethodSymbol true
//                    let chooseIntegerValueMethodSymbol = semanticModel.GetChooseValueMethodSymbol true SpecialType.System_Int32
//                    let chooseDecimalValueMethodSymbol = semanticModel.GetChooseValueMethodSymbol true SpecialType.System_Decimal
//                    let assignment value = transformAssignment symbolResolver semanticModel arguments.[0].Expression value
//
//                    if chooseBooleanValueMethodSymbol.Equals methodSymbol then
//                        GuardedCommandStatement [
//                            (BooleanLiteral true, assignment (BooleanLiteral true))
//                            (BooleanLiteral true, assignment (BooleanLiteral false))
//                        ]
//
//                    elif chooseDecimalValueMethodSymbol.Equals methodSymbol || chooseIntegerValueMethodSymbol.Equals methodSymbol then
//                        let expressions = arguments |> Seq.skip 1 |> Seq.map (fun argument -> transformExpression argument.Expression)
//                        let statements = expressions |> Seq.map (fun expression -> assignment expression)
//                        let clauses = statements |> Seq.map (fun statement -> (BooleanLiteral true, statement))
//                        clauses |> List.ofSeq |> GuardedCommandStatement
//                    else
//                        invalidOp "Unsupported C# Choose call: '%A'." invocation
//
//                | _ -> invalidOp "Encountered an unexpected C# syntax node: '%A'." <| statement.CSharpKind ()
//
//            | _ ->
//                 invalidOp "Encountered an unexpected C# syntax node: '%A'." <| statement.CSharpKind ()
//
//        transform statement
//
//    /// Transforms the body of the given method symbol.
//    let private transformMethodBody (compilation : Compilation) (symbolResolver : SymbolResolver) methodSymbol =
//        let csharpMethod = symbolResolver.ResolveCSharpMethod methodSymbol
//        let methodDeclaration = csharpMethod.GetMethodDeclaration ()
//        let semanticModel = csharpMethod.GetSemanticModel compilation
//
//        Transform symbolResolver semanticModel methodDeclaration.Body
//
//    /// Transforms the bodies of all of the component's methods.
//    let private transformComponentMethods compilation symbolResolver componentSymbol = 
//        let methods = seq {
//            match componentSymbol.UpdateMethod with
//            | None -> ()
//            | Some methodSymbol ->
//                yield methodSymbol
//            yield! componentSymbol.ProvidedPorts |> List.map (fun (ProvidedPort method') -> method')
//        }
//        methods |> Seq.map (fun methodSymbol -> ((componentSymbol, methodSymbol), transformMethodBody compilation symbolResolver methodSymbol))
//
//    /// Transforms the bodies of all methods declared by the components in the symbol resolver.
//    let TransformMethodBodies (compilation : Compilation) (symbolResolver : SymbolResolver) =
//        symbolResolver.ModelSymbol.ComponentSymbols 
//        |> Seq.collect (transformComponentMethods compilation symbolResolver)
//        |> Map.ofSeq