namespace NuXmvAstToFile

open NuXmvDataStructures.Ast
open System

type ExportNuXmvAstToFile() =

    let indent (number:int) : string =
        let s=System.Text.StringBuilder ()
        for i = 1 to number do 
            s.Append "  " |> ignore
        s.ToString ()

    let nl = Environment.NewLine
    
    let nli (i:int) =
        nl + (indent i)
        
    let joinWithWhitespace (lst:string list) : string =
        String.Join(" ", lst)

    let joinWithComma (lst:string list) : string =
        String.Join(", ", lst)
    
    let joinWithNewLine (lst:string list) : string =
        String.Join("\n", lst)
        
    let joinWith (operator:string) (lst:string list) : string =
        String.Join(operator, lst)
    
    // NuXmv is Two complement and Highest Bit in front (binary 10000 is decimal 16 not decimal 1)
    let BinaryArrayToBin (value:bool[]) : string =
        value |> Array.fold (fun acc elem -> if elem then acc+"1" else acc+"0") ""
    
    let BinaryArrayToHex (value:bool[]) : string =
        if value.Length % 4 <> 0 then
            failwith("Not convertable, because radix not mod 4")
        let stringBuilder = new System.Text.StringBuilder()
        let hexnumbers = value.Length / 4
        for i = 0 to hexnumbers-1 do
            let n8 = if value.[i*4]     then 8 else 0
            let n4 = if value.[i*4 + 1] then 4 else 0
            let n2 = if value.[i*4 + 2] then 2 else 0
            let n1 = if value.[i*4 + 3] then 1 else 0
            stringBuilder.Append((n8+n4+n2+n1).ToString("X")) |>ignore
        stringBuilder.ToString()

    let BinaryArrayToOctal (value:bool[]) : string =
        if value.Length % 3 <> 0 then
            failwith("Not convertable, because radix not mod 3")
        let stringBuilder = new System.Text.StringBuilder()
        let octalnumbers = value.Length / 3
        for i = 0 to octalnumbers-1 do
            let n4 = if value.[i*3]     then 4 else 0
            let n2 = if value.[i*3 + 1] then 2 else 0
            let n1 = if value.[i*3 + 2] then 1 else 0
            stringBuilder.Append((n4+n2+n1).ToString()) |>ignore
        stringBuilder.ToString()

    let UnsignedBinaryArrayToDecimal (value:bool[]) : string =
        let arrayReverse = Array.rev value
        let (endValue,pot) : int*int =
            Array.fold (fun (acc,pot) elem -> if elem then (acc+pot,pot*2) else (acc,pot*2)) (0,1) arrayReverse
        endValue.ToString()

    let SignedBinaryArrayToDecimal (value:bool[]) : string =
        if value.Length < 2 then
            "0"
        else
            let isPositive = value.[0]
            let number = value.[1..]
            if isPositive then
                UnsignedBinaryArrayToDecimal number
            else
                let arrayReverse = Array.rev number
                let (valueMinusOne,pot) : int*int =
                    //here we threat every bit as if it was negated
                    Array.fold (fun (acc,pot) elem -> if elem then (acc,pot*2) else (acc+pot,pot*2)) (0,1) arrayReverse
                sprintf "-%s" ((valueMinusOne+1).ToString())

    // printOptionalArgument uses the function "exporter" on the argument "opt" if "opt" is available and outputs the result. Otherwise it outputs the empty string ""
    // Example:
    //    Assume this.ExportPriority operates on an "unboxed" Priority-Value and outputs a String
    //    The following function operates on "boxed" Priority-Values (Priority option) and outputs the result of the this.ExportPriority and adds two whitespaces around the result
    //       let printPriority (priority : Priority option) : String = printOptionalArgument priority (fun a -> " " + this.ExportPriority a + " ")
    //    Unfolded it would be something like
    //       let printPriority (priority : Priority option) : String =
    //         match priority with
    //             | Some(priority) -> " " + (this.ExportPriority priority) + " "
    //             | None -> ""
    let printOptionalArgument (opt : 'a option) exporter : String =
        match opt with
            | Some(opt) -> exporter opt + " "
            | None -> ""

    
    //We keep approximately the order of the Ast in NuXmvAst.fs. Operators are introduced when needed
        
    member this.ExportIdentifier (identifier : Identifier) = 
        identifier.Name
    
    member this.ExportComplexIdentifier (complexIdentifier : ComplexIdentifier) =
        match complexIdentifier with
            | NameComplexIdentifier (nameIdentifier:Identifier) ->
                // NestedComplexIdentifier : Identifier
                this.ExportIdentifier nameIdentifier
            | NestedComplexIdentifier (container:ComplexIdentifier,nameIdentifier:Identifier) ->
                // NestedComplexIdentifier : Container '.' NameIdentifier
                sprintf "%s.%s" (this.ExportComplexIdentifier container) (this.ExportIdentifier nameIdentifier)
            | ArrayAccessComplexIdentifier (container:ComplexIdentifier, index:SimpleExpression) ->
                // NestedComplexIdentifier : Container '[' Index ']'
                sprintf "%s[%s]" (this.ExportComplexIdentifier container) (this.ExportSimpleExpression index)
            | SelfComplexIdentfier ->
                "self"

    member this.ExportTypeSpecifier (typeSpecifier:TypeSpecifier) =
        match typeSpecifier with
            | SimpleTypeSpecifier (specifier:SimpleTypeSpecifier) -> this.ExportSimpleTypeSpecifier specifier
            | ModuleTypeSpecifier (specifier:ModuleTypeSpecifier) -> this.ExportModuleTypeSpecifier specifier

// The types themselves are only used internally. The declaration of variables
// in the smv-file may use expression to define e.g. the lower and upper bound 
// of an array, the number of bytes of a word, etc...
    member this.ExportType (_type:Type) =
        failwith "NotImplemented"
        (*
        match _type with
            | BooleanType
            | EnumerationType of Domain:(ConstExpression list)
            | UnsignedWordType of Length:int  //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
            | SignedWordType of Length:int    //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
            | IntegerType
            | RealType
            | ArrayType of Lower:int * Upper:int *ElementType:Type
            | SetType //this one is todo
        *)


    member this.ExportSimpleTypeSpecifier (simpleTypeSpecifier:SimpleTypeSpecifier) =
        match simpleTypeSpecifier with
            | BooleanTypeSpecifier ->
                "boolean"
            | UnsignedWordTypeSpecifier (length:BasicExpression) -> 
                sprintf "unsigned word [%s]" (this.ExportBasicExpression length) //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
            | SignedWordTypeSpecifier (length:BasicExpression) ->
                sprintf "signed word [%s]" (this.ExportBasicExpression length) //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
            | RealTypeSpecifier ->
                "real"
            | IntegerTypeSpecifier ->
                "integer"
            | EnumerationTypeSpecifier (domain:(ConstExpression list)) ->
                let content =
                    domain |> List.map (fun constExpr -> this.ExportConstExpression constExpr)
                           |> joinWithWhitespace 
                sprintf "{ %s }" content // TODO: "HasSymbolicConstants" and "HasIntegerNumbers" Method, "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum,Integer-Enum}
            | IntegerRangeTypeSpecifier (lower:BasicExpression, upper:BasicExpression) ->
                sprintf "%s .. %s" (this.ExportBasicExpression lower) (this.ExportBasicExpression upper)
            | ArrayTypeSpecifier (lower:BasicExpression, upper:BasicExpression,elementType:SimpleTypeSpecifier) ->
                sprintf "array %s..%s of %s" (this.ExportBasicExpression lower) (this.ExportBasicExpression upper) (this.ExportSimpleTypeSpecifier elementType)
             

    member this.ExportConstExpression (constExpression:ConstExpression) =
        match constExpression with
            | BooleanConstant (value:bool) ->
                match value with
                    | true -> "TRUE"
                    | false -> "FALSE"
            | SymbolicConstant (symbolName:Identifier) ->
                this.ExportIdentifier symbolName
            | IntegerConstant (value:System.Numerics.BigInteger) ->
                value.ToString()
            | RealConstant (value:float) ->
                value.ToString()
            | WordConstant (value:(bool[]), sign:SignSpecifier, _base:Radix, improveReadability:bool) ->
                //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement   
                let (isSigned,signSpecifierStr) =
                    match sign with
                        | UnsignedSpecifier -> (false,"u")
                        | SignedSpecifier -> (true,"s")
                let (baseStr,numberStr) =
                    match _base with
                        | BinaryRadix -> ("b",BinaryArrayToBin value)
                        | OctalRadix -> ("o",BinaryArrayToOctal value)
                        | DecimalRadix -> ("d",if isSigned then SignedBinaryArrayToDecimal value else UnsignedBinaryArrayToDecimal value)
                        | HexadecimalRadix -> ("h",BinaryArrayToHex value)
                //TODO: improveReadability
                sprintf "0%s%s%s_%s" signSpecifierStr baseStr (value.Length.ToString()) numberStr                
            | RangeConstant (from:System.Numerics.BigInteger, _to:System.Numerics.BigInteger) ->
                sprintf "%s..%s" (from.ToString()) (_to.ToString())

    member this.ExportBasicExpression (basicExpression:BasicExpression) =
        match basicExpression with
            | ConstExpression (constExpression) ->
                this.ExportConstExpression constExpression
            | ComplexIdentifierExpression (identifier:ComplexIdentifier) ->
                //Identifier is the reference to a variable or a define. Might be hierarchical.
                this.ExportComplexIdentifier identifier
            | UnaryExpression (operator:UnaryOperator, operand:BasicExpression) ->
                match operator with
                    | UnaryOperator.LogicalNot -> sprintf "(! %s)" (this.ExportBasicExpression operand)
            | BinaryExpression (left:BasicExpression, operator:BinaryOperator, right:BasicExpression) ->
                let left = this.ExportBasicExpression left
                let right = this.ExportBasicExpression right
                let opStr = match operator with
                                | BinaryOperator.LogicalAnd             -> "&"
                                | BinaryOperator.LogicalOr              -> "|"
                                | BinaryOperator.LogicalXor             -> "xor"
                                | BinaryOperator.LogicalNxor            -> "nxor"
                                | BinaryOperator.LogicalImplies         -> "->"
                                | BinaryOperator.LogicalEquivalence     -> "<->"
                                | BinaryOperator.Equality               -> "="
                                | BinaryOperator.Inequality             -> "!="
                                | BinaryOperator.LessThan               -> "<"
                                | BinaryOperator.GreaterThan            -> ">"
                                | BinaryOperator.LessEqual              -> "<="
                                | BinaryOperator.GreaterEqual           -> ">="
                                | BinaryOperator.IntegerAddition        -> "+"
                                | BinaryOperator.IntegerSubtraction     -> "-|"
                                | BinaryOperator.IntegerMultiplication  -> "*"
                                | BinaryOperator.IntegerDivision        -> "/"
                                | BinaryOperator.IntegerRemainder       -> "mod"
                                | BinaryOperator.BitShiftRight          -> ">>"
                                | BinaryOperator.BitShiftLeft           -> "<<"
                sprintf "( %s %s %s )" left opStr right
            | TenaryExpression -> 
                "" //TODO
            | IndexSubscriptExpression (expressionLeadingToArray:BasicExpression, index:BasicExpression) -> 
                //TODO: Validation, Index has to be word or integer
                sprintf "%s[%s]" (this.ExportBasicExpression expressionLeadingToArray) (this.ExportBasicExpression index)
            | SetExpression (setBodyExpressions:(BasicExpression list)) -> 
                // TODO there is another way to gain set-expressions by the union-operator. See page 19. Here we use the way by enumerating every possible value
                let content = setBodyExpressions |> List.map (fun elem -> this.ExportBasicExpression elem)
                                                 |> joinWithComma
                sprintf "{ %s }" content
            | CaseExpression (caseBody:(CaseConditionAndEffect list)) ->
                let ExportCaseConditionAndEffect (caseConditionAndEffect:CaseConditionAndEffect) =
                    sprintf "%s : %s;" (this.ExportBasicExpression caseConditionAndEffect.CaseCondition) (this.ExportBasicExpression caseConditionAndEffect.CaseEffect)
                let content = caseBody |> List.map ExportCaseConditionAndEffect
                                       |> joinWithNewLine
                sprintf "\ncase\n%s\nesac" content
            | BasicNextExpression (expression:BasicExpression) ->
                // TODO: Description reads as if argument is a SimpleExpression. Maybe introduce a validator or use simpleexpression. Basically it is also a unary operator, but with different validations
                sprintf "next(%s)" (this.ExportBasicExpression expression)

    member this.ExportSimpleExpression (basicExpression:BasicExpression) =
        this.ExportBasicExpression basicExpression

    member this.ExportNextExpression (basicExpression:BasicExpression) =
        this.ExportBasicExpression basicExpression
            
    member this.ExportModuleElement (moduleElement:ModuleElement) =
        let ExportVariable (variable:TypedIdentifier) =
            sprintf "%s : %s;" (this.ExportIdentifier variable.Identifier) (this.ExportTypeSpecifier variable.TypeSpecifier)
        let ExportVariableSimple (variable:SimpleTypedIdentifier) =
            sprintf "%s : %s;" (this.ExportIdentifier variable.Identifier) (this.ExportSimpleTypeSpecifier variable.TypeSpecifier)
        let ExportIdentifierNextExpressionTuple (identifierNextExpressionTuple:IdentifierNextExpressionTuple) =
            sprintf "%s := %s;" (this.ExportIdentifier identifierNextExpressionTuple.Identifier) (this.ExportNextExpression identifierNextExpressionTuple.Expression)
        match moduleElement with
            | VarDeclaration (variables:(TypedIdentifier list)) -> 
                // Chapter 2.3.1 Variable Declarations p 23-26. Type Specifiers are moved into Type-Namespace.                
                let content = variables |> List.map ExportVariable
                                        |> joinWithNewLine
                sprintf "VAR\n%s" content
            | IVarDeclaration (inputVariables:(SimpleTypedIdentifier list)) ->                
                let content = inputVariables |> List.map ExportVariableSimple
                                             |> joinWithNewLine
                sprintf "IVAR\n%s" content
            | FrozenVarDeclaration (frozenVariables:(SimpleTypedIdentifier list)) ->
                let content = frozenVariables |> List.map ExportVariableSimple
                                              |> joinWithNewLine
                sprintf "FROZENVAR\n%s" content
            | DefineDeclaration (defines:(IdentifierNextExpressionTuple list)) -> 
                //Chapter 2.3.2 DEFINE Declarations p 26
                let content = defines |> List.map ExportIdentifierNextExpressionTuple
                                      |> joinWithNewLine
                sprintf "DEFINE\n%s" content
            // TODO | ArrayDefineDeclaration // Chapter 2.3.3 Array Define Declarations p 26-27
            | ConstantsDeclaration (constants:(Identifier list)) ->
                // Chapter 2.3.4 CONSTANTS Declarations p 27
                let content = constants |> List.map this.ExportIdentifier
                                        |> joinWithComma
                sprintf "CONSTANTS\n%s" content
            | InitConstraint (expression:SimpleExpression) ->
                // Chapter 2.3.5 INIT Constraint p 27
                let content = this.ExportSimpleExpression expression
                sprintf "INIT\n%s" content
            | InvarConstraint (expression:SimpleExpression) ->
                // Chapter 2.3.6 INVAR Constraint p 27
                let content = this.ExportSimpleExpression expression
                sprintf "INVAR\n%s" content
            | TransConstraint (expression:NextExpression) ->
                // Chapter 2.3.7 TRANS Constraint p 28                
                let content = this.ExportSimpleExpression expression
                sprintf "TRANS\n%s" content
            | AssignConstraint (assigns:(SingleAssignConstraint list)) ->
                let ExportSingleAssignConstraint (singleAssignConstraint:SingleAssignConstraint) = 
                    // Chapter 2.3.8 ASSIGN Constraint p 28-29 (for AssignConstraint)
                    match singleAssignConstraint with
                        | CurrentStateAssignConstraint (identifier:Identifier, expression:SimpleExpression) -> 
                            sprintf "%s := %s;" (this.ExportIdentifier identifier) (this.ExportSimpleExpression expression)
                        | InitialStateAssignConstraint (identifier:Identifier, expression:SimpleExpression) ->
                            sprintf "init(%s) := %s;" (this.ExportIdentifier identifier) (this.ExportSimpleExpression expression)
                        | NextStateAssignConstraint (identifier:Identifier, expression:NextExpression) ->
                            sprintf "next(%s) := %s;" (this.ExportIdentifier identifier) (this.ExportSimpleExpression expression)
                // Chapter 2.3.8 ASSIGN Constraint p 28-29
                let content = assigns |> List.map ExportSingleAssignConstraint
                                      |> joinWithNewLine
                sprintf "ASSIGN\n%s" content
            // TODO | FairnessConstraint // Chapter 2.3.9 FAIRNESS Constraints p 30
            | SpecificationInModule (specification) -> 
                this.ExportSpecification specification
            // // Chapter 2.3.16 ISA Declarations p 34 (depreciated).Ddon't implement as it is depreciated
            | PredDeclaration (identifier:Identifier, expression:SimpleExpression) -> 
                // Chapter 2.3.17 PRED and MIRROR Declarations p 34-35. Useful for debugging and CEGAR (Counterexample Guided Abstraction Refinement)
                //TODO: optional
                sprintf "PRED <%s> :=  %s" (this.ExportIdentifier identifier) (this.ExportSimpleExpression expression)
            | MirrorDeclaration (variableIdentifier:ComplexIdentifier) -> 
                sprintf "MIRROR %s" (this.ExportComplexIdentifier variableIdentifier)


    member this.ExportModuleDeclaration (moduleDeclaration:ModuleDeclaration) = 
         // Chapter 2.3.10 MODULE Declarations p 30-31
        let name = this.ExportIdentifier moduleDeclaration.Identifier
        let parameterString =
            let parameterStringContent =
                moduleDeclaration.ModuleParameters |> List.map this.ExportIdentifier
                                                   |> joinWithComma
            if moduleDeclaration.ModuleParameters.Length > 0 then (sprintf "(%s)" parameterStringContent) else " "
        let content =
            moduleDeclaration.ModuleElements |> List.map this.ExportModuleElement
                                             |> joinWithNewLine
        sprintf "MODULE %s%s%s" name parameterString content
    


    member this.ExportModuleTypeSpecifier (moduleTypeSpecifier:ModuleTypeSpecifier) = 
        // Chapter 2.3.11 MODULE Instantiations p 31.
        let name = this.ExportIdentifier moduleTypeSpecifier.ModuleName
        let parameterString =
            let parameterStringContent =
                moduleTypeSpecifier.ModuleParameters |> List.map this.ExportBasicExpression
                                                     |> joinWithComma
            if moduleTypeSpecifier.ModuleParameters.Length > 0 then (sprintf "(%s)" parameterStringContent) else " "
        sprintf "%s%s" name parameterString


    member this.ExportNuXmvProgram (nuXmvProgram:NuXmvProgram) = 
        // Chapter 2.3.13 A Program and the main Module p 33
        let modules =
            nuXmvProgram.Modules |> List.map this.ExportModuleDeclaration
                                 |> joinWithNewLine
        let specifications =
            nuXmvProgram.Specifications |> List.map this.ExportSpecification
                                        |> joinWithNewLine
        sprintf "%s\n\n%s" modules specifications

    member this.ExportCtlExpression (ctlExpression:CtlExpression) =
        match ctlExpression with
            | CtlSimpleExpression (expression:SimpleExpression) ->
                this.ExportSimpleExpression expression
            | CtlUnaryExpression (operator:CtlUnaryOperator, operand:CtlExpression) ->
                let opStr = match operator with
                                | CtlUnaryOperator.LogicalNot      -> "!"
                                | CtlUnaryOperator.ExistsGlobally  -> "EG"
                                | CtlUnaryOperator.ExistsNextState -> "EX"
                                | CtlUnaryOperator.ExistsFinally   -> "EF"
                                | CtlUnaryOperator.ForallGlobally  -> "AG"
                                | CtlUnaryOperator.ForallNext      -> "AX"
                                | CtlUnaryOperator.ForallFinally   -> "AF"
                sprintf "(%s %s)" opStr (this.ExportCtlExpression operand)
            | CtlBinaryExpression (left:CtlExpression, operator:CtlBinaryOperator, right:CtlExpression) ->
                match operator with
                    | CtlBinaryOperator.LogicalAnd         -> sprintf "(%s & %s)" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.LogicalOr          -> sprintf "(%s | %s)" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.LogicalXor         -> sprintf "(%s xor %s)" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.LogicalNxor        -> sprintf "(%s nxor %s)" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.LogicalImplies     -> sprintf "(%s -> %s)" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.LogicalEquivalence -> sprintf "(%s <-> %s)" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.ExistsUntil        -> sprintf "(E [%s U %s])" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                    | CtlBinaryOperator.ForallUntil        -> sprintf "(A [%s U %s])" (this.ExportCtlExpression left) (this.ExportCtlExpression right)
                        
            
    member this.ExportLtlExpression (ltlExpression:LtlExpression) =
        match ltlExpression with
            | LtlSimpleExpression (expression:SimpleExpression) ->
                this.ExportSimpleExpression expression
            | LtlUnaryExpression (operator:LtlUnaryOperator,  operand:LtlExpression) ->
                let opStr = match operator with
                                | LtlUnaryOperator.LogicalNot              -> "!"
                                | LtlUnaryOperator.FutureNext              -> "X"
                                | LtlUnaryOperator.FutureGlobally          -> "G"
                                | LtlUnaryOperator.FutureFinally           -> "F"
                                | LtlUnaryOperator.PastPrevious            -> "Y"
                                | LtlUnaryOperator.PastNotPreviousStateNot -> "Z"
                                | LtlUnaryOperator.PastHistorically        -> "H"
                                | LtlUnaryOperator.PastOnce                -> "O"
                sprintf "(%s %s)" opStr (this.ExportLtlExpression operand)
            | LtlBinaryExpression (left:LtlExpression, operator:LtlBinaryOperator, right:LtlExpression) ->
                match operator with
                    | LtlBinaryOperator.LogicalAnd         -> sprintf "(%s & %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.LogicalOr          -> sprintf "(%s | %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.LogicalXor         -> sprintf "(%s xor %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.LogicalNxor        -> sprintf "(%s nxor %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.LogicalImplies     -> sprintf "(%s -> %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.LogicalEquivalence -> sprintf "(%s <-> %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.FutureUntil        -> sprintf "(%s U %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.FutureReleases     -> sprintf "(%s R %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.PastSince          -> sprintf "(%s S %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)
                    | LtlBinaryOperator.PastTriggered      -> sprintf "(%s T %s)" (this.ExportLtlExpression left) (this.ExportLtlExpression right)

    member this.ExportSpecification (specification:Specification) =
        match specification with
            | CtlSpecification (ctlExpression:CtlExpression) -> "CTLSPEC " + this.ExportCtlExpression ctlExpression
            | LtlSpecification (ltlExpression:LtlExpression) -> "LTLSPEC " + this.ExportLtlExpression ltlExpression
        

    (*
    // Operators
    type UnaryOperator = 
        | LogicalNot

    type BinaryOperator=      
        | LogicalAnd
        | LogicalOr
        | LogicalXor
        | LogicalNxor
        | LogicalImplies
        | LogicalEquivalence
        | Equality
        | Inequality
        | LessThan
        | GreaterThan
        | LessEqual
        | GreaterEqual
        | IntegerAddition
        | IntegerSubtraction
        | IntegerMultiplication
        | IntegerDivision
        | IntegerRemainder
        | BitShiftRight
        | BitShiftLeft

   *)