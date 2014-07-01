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

open System
open System.Linq.Expressions
open System.Reflection
open SafetySharp.Internal.Metamodel
open SafetySharp.Modeling
open SafetySharp.Internal.Utilities

type LinqExpression = System.Linq.Expressions.Expression

module internal FormulaTransformation =
    
    /// Applies the given projection to the expression if the expression is of the required type.
    let private projectExpression (expression : LinqExpression) projection =
        match expression with
        | :? 'T as expression -> Some <| projection expression
        | _ -> None

    /// Matches a Linq constant expression, returning the constant's value.
    let private (|ConstantExpression|_|) (expression : LinqExpression) =
        projectExpression expression <| fun (expression : ConstantExpression) -> expression.Value

    /// Matches a Linq member access, returning the object expression and the member info of the accessed member.
    let private (|MemberExpression|_|) (expression : LinqExpression) =
        projectExpression expression <| fun (expression : MemberExpression) -> (expression.Expression, expression.Member)

    /// Matches a unary Linq expression representing a conversion, returning the operand as well as the conversion method.
    let private (|ConversionExpression|_|) (expression : LinqExpression) =
        match expression with
        | :? UnaryExpression as expression when expression.NodeType = ExpressionType.Convert ->
            Some (expression.Operand, expression.Method)
        | _ -> None

    /// Matches a unary Linq expression, returning the operand as well as the operator.
    let private (|UnaryExpression|_|) (expression : LinqExpression) =
        projectExpression expression <| fun (expression : UnaryExpression) -> (expression.Operand, expression.NodeType)

    /// Matches a binary Linq expression, returning the both operands as well as the operator.
    let private (|BinaryExpression|_|) (expression : LinqExpression) =
        projectExpression expression <| fun (expression : BinaryExpression) -> (expression.Left, expression.NodeType, expression.Right)

    /// Matches a Linq lambda expression, returning its parameters, return type, and body.
    let private (|LambdaExpression|_|) (expression : LinqExpression) =
        projectExpression expression <| fun (expression : LambdaExpression) -> 
            (expression.Parameters |> List.ofSeq, expression.ReturnType, expression.Body)

    /// Converts the given value to a metamodel literal expression.
    let private convertConstant (value : obj) =
        match value with
        | :? bool as value -> BooleanLiteral value
        | :? int as value -> IntegerLiteral value
        | :? decimal as value -> DecimalLiteral value
        | _ when value.GetType().IsEnum -> IntegerLiteral (value :?> int)
        | _ -> invalidOp "Constants of type '%s' are not supported within formulas." <| value.GetType().FullName

    /// Gets the CLR object represented by the Linq expression.
    let rec private getValue (expression : LinqExpression) =
        match expression with
        | ConstantExpression value -> value
        | MemberExpression (expression, memberInfo) ->
            let object' = getValue expression
            match memberInfo with
            | :? FieldInfo as fieldInfo -> fieldInfo.GetValue object'
            | :? PropertyInfo as propertyInfo when propertyInfo.CanRead -> propertyInfo.GetValue object'
            | _ -> invalidOp "Invalid member access: '%A'." expression
        | _ -> invalidOp "Invalid expression type while trying to retrieve member value: '%A'." expression.NodeType

    /// Transforms a component field access. 
    let private transformComponentFieldAccess (symbolResolver : SymbolResolver) (objectResolver : ObjectResolver) (component' : IComponent) fieldName =
        let component' = component' :?> Component
        if not <| objectResolver.CanResolve component' then
            UnknownComponentException component' |> raise
        let componentSymbol = symbolResolver.ResolveComponent component'
        let componentReferenceSymbol = symbolResolver.ResolveComponentReference component'
        match componentSymbol.Fields |> Seq.tryFind (fun fieldSymbol -> fieldSymbol.Name = fieldName) with
        | None -> invalidOp "Unable to find component field '%s.%s'." (component'.GetType().FullName) fieldName
        | Some fieldSymbol -> ReadField (fieldSymbol, Some componentReferenceSymbol)

    /// Checks whether the given method info represents the implicit conversion operator of <see cref="MemberAccess{T}" />.
    let private isImplicitMemberAccessConversion (methodInfo : MethodInfo) =
        methodInfo = typeof<MemberAccess<obj>>.GetGenericTypeDefinition().MakeGenericType(methodInfo.ReturnType).GetMethod("op_Implicit")

    /// Transforms C# formulas to metamodel formulas.
    let Transform (symbolResolver : SymbolResolver) (objectResolver : ObjectResolver) (formula : CSharpFormula) =

        // Transforms the given Linq expression to a metamodel expression.
        let rec transformLinqExpression (expression : LinqExpression) =
            match expression with
            | ConstantExpression value ->
                convertConstant value

            | MemberExpression (objectExpression, memberInfo) ->
                if typeof<IComponent>.IsAssignableFrom objectExpression.Type then
                    if not <| memberInfo :? FieldInfo then
                        invalidOp "Invalid component property access in formula: '%A'." expression
                    let component' = (getValue objectExpression) :?> Component
                    let fieldName = memberInfo.Name
                    transformComponentFieldAccess symbolResolver objectResolver component' fieldName
                elif typeof<IMemberAccess>.IsAssignableFrom expression.Type then
                    let memberAccess = getValue expression :?> IMemberAccess
                    transformComponentFieldAccess symbolResolver objectResolver memberAccess.Component memberAccess.MemberName
                elif objectExpression.Type.IsEnum then
                    let fieldInfo = memberInfo :?> FieldInfo
                    IntegerLiteral (fieldInfo.GetValue null :?> int)
                else
                    getValue expression |> convertConstant

            // We'll skip over 'enum literal to int' conversions
            | ConversionExpression (operand, conversionMethod) when operand.Type.IsEnum ->
                transformLinqExpression operand

            // We'll skip over conversion expressions that result from invoking the implicit conversion operator
            // of a MemberAccess instance. Other conversions are not supported within formulas.
            | ConversionExpression (operand, conversionMethod) when isImplicitMemberAccessConversion conversionMethod ->
                transformLinqExpression operand

            | UnaryExpression (operand, operator) ->
                match operator with
                | ExpressionType.Negate -> UnaryExpression (transformLinqExpression operand, UnaryOperator.Minus)
                | ExpressionType.Not -> UnaryExpression (transformLinqExpression operand, UnaryOperator.LogicalNot)
                | ExpressionType.UnaryPlus -> transformLinqExpression operand
                | _ -> invalidOp "Unsupported unary expression operator in formula: '%A'." expression.NodeType

            | BinaryExpression (leftOperand, operator, rightOperand) ->
                let operator = 
                    match operator with
                    | ExpressionType.Add -> BinaryOperator.Add
                    | ExpressionType.Subtract -> BinaryOperator.Subtract
                    | ExpressionType.Multiply -> BinaryOperator.Multiply
                    | ExpressionType.Divide -> BinaryOperator.Divide
                    | ExpressionType.Modulo -> BinaryOperator.Modulo
                    | ExpressionType.And | ExpressionType.AndAlso -> BinaryOperator.LogicalAnd
                    | ExpressionType.Or | ExpressionType.OrElse -> BinaryOperator.LogicalOr
                    | ExpressionType.Equal -> BinaryOperator.Equals
                    | ExpressionType.NotEqual -> BinaryOperator.NotEquals
                    | ExpressionType.GreaterThan -> BinaryOperator.GreaterThan
                    | ExpressionType.GreaterThanOrEqual -> BinaryOperator.GreaterThanOrEqual
                    | ExpressionType.LessThan -> BinaryOperator.LessThan
                    | ExpressionType.LessThanOrEqual -> BinaryOperator.LessThanOrEqual
                    | _ -> invalidOp "Unsupported binary expression operator in formula: '%A'." expression.NodeType
                BinaryExpression (transformLinqExpression leftOperand, operator, transformLinqExpression rightOperand)
 
            | _ -> 
                invalidOp "Unsupported C# expression type in formula: '%A'." expression.NodeType

        // Parses a Linq expression representing a state formula, skipping over the outer most lambda.
        let transformStateFormula (expression : LinqExpression) =
            match expression with
            | LambdaExpression (parameters, returnType, body) when parameters = [] && returnType = typeof<bool> ->
                transformLinqExpression body
            | _ -> invalidOp "Invalid C# statement expression within formula. Expected a lambda function of type '() -> bool'."

        // Transforms the given CSharp formula to a metamodel formula.
        let rec transform formula = 
            match formula with
            | CSharpStateFormula expression ->
                transformStateFormula expression |> StateFormula
            | CSharpUnaryFormula (operand, operator) -> 
                UnaryFormula (transform operand, operator)
            | CSharpBinaryFormula (leftOperand, operator, rightOperand) -> 
                BinaryFormula (transform leftOperand, operator, transform rightOperand)

        transform formula