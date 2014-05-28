namespace SafetySharp.FSharp.Formulas

open System
open System.IO
open System.Runtime.InteropServices
open FParsec
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

type BinaryOperator = 
    | And
    | Or
    | Implication
    | Equivalence
    | Until
    | AllPathsUntil
    | ExistsPathUntil

type UnaryOperator = 
    | Not
    | Next
    | Finally
    | Globally
    | AllPathsNext
    | AllPathsFinally
    | AllPathsGlobally
    | ExistsPathNext
    | ExistsPathFinally
    | ExistsPathGlobally

type Formula = 
    | ExpressionFormula of Expression : ExpressionSyntax
    | UnaryFormula of Operator : UnaryOperator * Operand : Formula
    | BinaryFormula of LeftOperand : Formula * Operator : BinaryOperator * RightOperand : Formula

[<AbstractClass>]
type FormulaVisitor () =
    member this.Visit formula =
        let rec visit = function
            | ExpressionFormula expression -> this.VisitExpressionFormula expression
            | UnaryFormula (operator, operand) -> this.VisitUnaryFormula operator operand
            | BinaryFormula (left, operator, right) -> this.VisitBinaryFormula left operator right

        visit formula

    abstract member VisitExpressionFormula: expression : ExpressionSyntax -> unit
    abstract member VisitUnaryFormula: operator : UnaryOperator -> operand : Formula -> unit
    abstract member VisitBinaryFormula: leftOperand : Formula -> operator : BinaryOperator -> rightOperand : Formula -> unit

type internal UnaryOperatorMetadata = { 
    Token : string
    Precedence : int
    Associative : bool
    Operation : UnaryOperator
}

type internal BinaryOperatorMetadata = { 
    Token : string
    Precedence : int
    Associativity : Associativity
    Operation : BinaryOperator
}

type FormulaParser() = 
    static member private UnaryOperators = [
        { Token = "!"; Precedence = 100; Associative = true; Operation = UnaryOperator.Not }
        { Token = "X"; Precedence = 10; Associative = true; Operation = UnaryOperator.Next}
        { Token = "F"; Precedence = 10; Associative = true; Operation = UnaryOperator.Finally }
        { Token = "G"; Precedence = 10; Associative = true; Operation = UnaryOperator.Globally }
        { Token = "AX"; Precedence = 10; Associative = true; Operation = UnaryOperator.Next}
        { Token = "AF"; Precedence = 10; Associative = true; Operation = UnaryOperator.Finally }
        { Token = "AG"; Precedence = 10; Associative = true; Operation = UnaryOperator.Globally }
        { Token = "EX"; Precedence = 10; Associative = true; Operation = UnaryOperator.Next}
        { Token = "EF"; Precedence = 10; Associative = true; Operation = UnaryOperator.Finally }
        { Token = "EG"; Precedence = 10; Associative = true; Operation = UnaryOperator.Globally }
    ]

    static member private BinaryOperators = [
        { Token = "&&"; Precedence = 60; Associativity = Associativity.Left; Operation = BinaryOperator.And }
        { Token = "||"; Precedence = 50; Associativity = Associativity.Left; Operation = BinaryOperator.Or }
        { Token = "=>"; Precedence = 40; Associativity = Associativity.Left; Operation = BinaryOperator.Implication }
        { Token = "<=>"; Precedence = 40; Associativity = Associativity.Left; Operation = BinaryOperator.Equivalence }
        { Token = "U"; Precedence = 20; Associativity = Associativity.Left; Operation = BinaryOperator.Until }
        { Token = "AU"; Precedence = 20; Associativity = Associativity.Left; Operation = BinaryOperator.AllPathsUntil }
        { Token = "EU"; Precedence = 20; Associativity = Associativity.Left; Operation = BinaryOperator.ExistsPathUntil }
    ]

    static member private ExpressionParser = 
        let openBrace = skipChar '{' .>> spaces
        let closeBrace = skipChar '}' .>> spaces

        let csharpExpression = manySatisfy (function '}' -> false | _ -> true)
        let parser = between openBrace closeBrace csharpExpression <?> "expression in curly braces"
        parser |>> FormulaParser.ParseCSharpExpression

    static member private FormulaParser =
        let parser = new OperatorPrecedenceParser<_,_,_>()

        let addInfixOperator { Token = token; Precedence = p; Associativity = a; Operation = o } = 
            parser.AddOperator(InfixOperator(token, spaces, p, a, fun e1 e2 -> BinaryFormula(e1, o, e2)))

        let addPrefixOperator { Token = token; Precedence = p; Associative = a; Operation = o } =
            parser.AddOperator(PrefixOperator(token, spaces, p, a, fun e -> UnaryFormula(o, e)))

        FormulaParser.UnaryOperators |> List.iter addPrefixOperator
        FormulaParser.BinaryOperators |> List.iter addInfixOperator
                
        let openParenthesis = skipChar '(' .>> spaces
        let closeParenthesis = skipChar ')' .>> spaces

        let expressionParser = parser.ExpressionParser
        let parenthesizedExpressionParser = between openParenthesis closeParenthesis expressionParser
        let parenthesizedExpressionParser = parenthesizedExpressionParser <?> "parenthesized expression"

        parser.TermParser <- parenthesizedExpressionParser <|> FormulaParser.ExpressionParser
        expressionParser

    static member private ParseCSharpExpression expression =
        let expression = SyntaxFactory.ParseExpression expression
//        let emitDiagnostic 

        ExpressionFormula expression

    static member TryParse(formula, addDiagnostic : Action<string>, [<Out>] parsedFormula : byref<Formula>) =
        match runParserOnString FormulaParser.FormulaParser (addDiagnostic.Invoke) "" formula with
        | Success(formula, _, _) ->
            parsedFormula <- formula
            true
        | Failure(msg, error, _) ->
            use writer = new StringWriter()
            error.WriteTo(writer, null, columnWidth = 200)
            let error = writer.ToString();
            addDiagnostic.Invoke error
            false
