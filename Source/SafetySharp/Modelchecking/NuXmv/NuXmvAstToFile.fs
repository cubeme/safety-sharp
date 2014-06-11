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
            | ConstExpression (constExpression) -> ""
            | ComplexIdentifierExpression (identifier:ComplexIdentifier) -> "" //Identifier is the reference to a variable or a define. Might be hierarchical.
            | UnaryExpression (operator:UnaryOperator, operand:BasicExpression) -> ""
            | BinaryExpression (left:BasicExpression, operator:BinaryOperator, right:BasicExpression) -> ""
            | TenaryExpression -> "" //TODO
            | IndexSubscriptExpression (expressionLeadingToArray:BasicExpression, index:BasicExpression) -> "" //TODO: Validation, Index has to be word or integer
            | SetExpression (setBodyExpressions:(BasicExpression list)) -> "" // TODO there is another way to gain set-expressions by the union-operator. See page 19. Here we use the way by enumerating every possible value
            | CaseExpression (caseBody:(CaseConditionAndEffect list)) -> ""
                (*let ExportCaseConditionAndEffect (caseConditionAndEffect:CaseConditionAndEffect)) -> "" = {
                    CaseCondition:BasicExpression;
                    CaseEffect:BasicExpression; *)
            | BasicNextExpression (expression:BasicExpression) -> "" // TODO: Description reads as if argument is a SimpleExpression. Maybe introduce a validator or use simpleexpression. Basically it is also a unary operator, but with different validations

    member this.ExportSimpleExpression (basicExpression:BasicExpression) =
        this.ExportBasicExpression basicExpression

    member this.ExportNextExpression (basicExpression:BasicExpression) =
        this.ExportBasicExpression basicExpression

    member this.ExportSingleAssignConstraint (singleAssignConstraint:SingleAssignConstraint) = // Chapter 2.3.8 ASSIGN Constraint p 28-29 (for AssignConstraint)
        match singleAssignConstraint with
            | CurrentStateAssignConstraint (identifier:Identifier, expression:SimpleExpression) -> "" //Invariant which must evaluate to true. next-Statement is forbidden inside
            | InitialStateAssignConstraint (identifier:Identifier, expression:SimpleExpression) -> "" //Invariant which must evaluate to true. next-Statement is forbidden inside
            | NextStateAssignConstraint (identifier:Identifier, expression:NextExpression) -> ""

    member this.ExportModuleElement (moduleElement:ModuleElement) =
        match moduleElement with
            | VarDeclaration (variables:(TypedIdentifier list)) -> "" // Chapter 2.3.1 Variable Declarations p 23-26. Type Specifiers are moved into Type-Namespace.
            | IVarDeclaration (inputVariables:(SimpleTypedIdentifier list)) -> ""
            | FrozenVarDeclaration (frozenVariables:(SimpleTypedIdentifier list)) -> "" //Array (frozen variable declarations (readonly, nondeterministic initialization
            | DefineDeclaration (defines:(IdentifierNextExpressionTuple list)) -> "" // Chapter 2.3.2 DEFINE Declarations p 26
            // TODO | ArrayDefineDeclaration // Chapter 2.3.3 Array Define Declarations p 26-27
            | ConstantsDeclaration (constants:(Identifier list)) -> "" // Chapter 2.3.4 CONSTANTS Declarations p 27
            | InitConstraint (expression:SimpleExpression) -> "" // Chapter 2.3.5 INIT Constraint p 27
            | InvarConstraint (expression:SimpleExpression) -> "" // Chapter 2.3.6 INVAR Constraint p 27
            | TransConstraint (expression:NextExpression) -> "" // Chapter 2.3.7 TRANS Constraint p 28
            | AssignConstraint (assigns:(SingleAssignConstraint list)) -> "" // Chapter 2.3.8 ASSIGN Constraint p 28-29
            // TODO | FairnessConstraint // Chapter 2.3.9 FAIRNESS Constraints p 30
            | SpecificationInModule (specification) -> ""
            // // Chapter 2.3.16 ISA Declarations p 34 (depreciated).Ddon't implement as it is depreciated
            | PredDeclaration (identifier:Identifier, expression:SimpleExpression) -> ""// Chapter 2.3.17 PRED and MIRROR Declarations p 34-35. Useful for debugging and CEGAR (Counterexample Guided Abstraction Refinement)
            | MirrorDeclaration (variableIdentifier:ComplexIdentifier) -> ""


    member this.ExportModuleDeclaration (moduleDeclaration:ModuleDeclaration) = 
        ""
    (*{ // Chapter 2.3.10 MODULE Declarations p 30-31
        Identifier:Identifier;
        ModuleParameters:Identifier list;
        ModuleElements:ModuleElement list;
 }*)


    member this.ExportModuleTypeSpecifier (moduleTypeSpecifier:ModuleTypeSpecifier) = 
        ""
    (*{// Chapter 2.3.11 MODULE Instantiations p 31.
        ModuleName:Identifier;
        ModuleParameters:BasicExpression list;
}*)


    member this.ExportNuXmvProgram (nuXmvProgram:NuXmvProgram) = 
        ""
    (*{ // Chapter 2.3.13 A Program and the main Module p 33
    Modules:ModuleDeclaration list;
    Specifications:Specification list;
}*)

    member this.ExportCtlExpression (ctlExpression:CtlExpression) =
        match ctlExpression with
            | CtlSimpleExpression (expression:SimpleExpression) -> ""
            | CtlUnaryExpression (operator:CtlUnaryOperator, operand:CtlExpression) -> ""
            | CtlBinaryExpression (left:CtlExpression, operator:CtlBinaryOperator, right:CtlExpression) -> ""
            
    member this.ExportLtlExpression (ltlExpression:LtlExpression) =
        match ltlExpression with
            | LtlSimpleExpression (expression:SimpleExpression) -> ""
            | LtlUnaryExpression (operator:LtlUnaryOperator,  operand:LtlExpression) -> ""
            | LtlBinaryExpression (left:LtlExpression, operator:LtlBinaryOperator, right:LtlExpression) -> ""

    member this.ExportSpecification (specification:Specification) =
        match specification with
            | CtlSpecification (ctlExpression:CtlExpression) -> ""
            | LtlSpecification (ltlExpression:LtlExpression) -> ""
        

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