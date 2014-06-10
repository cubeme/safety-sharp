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
                ""
            | ArrayAccessComplexIdentifier (container:ComplexIdentifier, index:SimpleExpression) ->
                // NestedComplexIdentifier : Container '[' Index ']'
                ""
            | SelfComplexIdentfier ->
                "self"

    member this.ExportTypeSpecifier (typeSpecifier:TypeSpecifier) =
        match typeSpecifier with
            | SimpleTypeSpecifier (specifier:SimpleTypeSpecifier) -> ""
            | ModuleTypeSpecifier (specifier:ModuleTypeSpecifier) -> ""

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
            | BooleanTypeSpecifier -> ""
            | UnsignedWordTypeSpecifier (Length:BasicExpression) -> ""  //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
            | SignedWordTypeSpecifier (Length:BasicExpression) -> ""    //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
            | RealTypeSpecifier -> ""
            | IntegerTypeSpecifier -> ""
            | EnumerationTypeSpecifier (Domain:(ConstExpression list)) -> "" // TODO: "HasSymbolicConstants" and "HasIntegerNumbers" Method, "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum,Integer-Enum}
            | IntegerRangeTypeSpecifier (Lower:BasicExpression, Upper:BasicExpression) -> ""
            | ArrayTypeSpecifier (Lower:BasicExpression, Upper:BasicExpression,ElementType:SimpleTypeSpecifier) -> ""
             

    member this.ExportConstExpression (constExpression:ConstExpression) =
        let ExportRadix (radix:Radix) =
            match radix with
                | BinaryRadix -> ""
                | OctalRadix -> ""
                | DecimalRadix -> ""
                | HexadecimalRadix -> ""  
        let ExportSignSpecifier (signSpecifier:SignSpecifier) =
            match signSpecifier with
                | UnsignedSpecifier -> ""
                | SignedSpecifier -> ""
        match constExpression with
            | BooleanConstant (Value:bool) -> ""
            | SymbolicConstant (SymbolName:Identifier) -> ""
            | IntegerConstant (Value:System.Numerics.BigInteger) -> ""
            | RealConstant (Value:float) -> ""
            | WordConstant (Value:(bool list), Sign:SignSpecifier, Base:Radix, ImproveReadability:bool) -> ""
            | RangeConstant (From:System.Numerics.BigInteger, To:System.Numerics.BigInteger) -> ""

    member this.ExportBasicExpression (basicExpression:BasicExpression) =
        match basicExpression with
            | ConstExpression (constExpression) -> ""
            | ComplexIdentifierExpression (Identifier:ComplexIdentifier) -> "" //Identifier is the reference to a variable or a define. Might be hierarchical.
            | UnaryExpression (operator:UnaryOperator, operand:BasicExpression) -> ""
            | BinaryExpression (Left:BasicExpression, Operator:BinaryOperator, Right:BasicExpression) -> ""
            | TenaryExpression -> "" //TODO
            | IndexSubscriptExpression (ExpressionLeadingToArray:BasicExpression, Index:BasicExpression) -> "" //TODO: Validation, Index has to be word or integer
            | SetExpression (SetBodyExpressions:(BasicExpression list)) -> "" // TODO there is another way to gain set-expressions by the union-operator. See page 19. Here we use the way by enumerating every possible value
            | CaseExpression (CaseBody:(CaseConditionAndEffect list)) -> ""
                (*let ExportCaseConditionAndEffect (caseConditionAndEffect:CaseConditionAndEffect)) -> "" = {
                    CaseCondition:BasicExpression;
                    CaseEffect:BasicExpression; *)
            | BasicNextExpression (Expression:BasicExpression) -> "" // TODO: Description reads as if argument is a SimpleExpression. Maybe introduce a validator or use simpleexpression. Basically it is also a unary operator, but with different validations

    member this.ExportSingleAssignConstraint (singleAssignConstraint:SingleAssignConstraint) = // Chapter 2.3.8 ASSIGN Constraint p 28-29 (for AssignConstraint)
        match singleAssignConstraint with
            | CurrentStateAssignConstraint (Identifier:Identifier, Expression:SimpleExpression) -> "" //Invariant which must evaluate to true. next-Statement is forbidden inside
            | InitialStateAssignConstraint (Identifier:Identifier, Expression:SimpleExpression) -> "" //Invariant which must evaluate to true. next-Statement is forbidden inside
            | NextStateAssignConstraint (Identifier:Identifier, Expression:NextExpression) -> ""

    member this.ExportModuleElement (moduleElement:ModuleElement) =
        match moduleElement with
            | VarDeclaration (Variables:(TypedIdentifier list)) -> "" // Chapter 2.3.1 Variable Declarations p 23-26. Type Specifiers are moved into Type-Namespace.
            | IVarDeclaration (InputVariables:(SimpleTypedIdentifier list)) -> ""
            | FrozenVarDeclaration (FrozenVariables:(SimpleTypedIdentifier list)) -> "" //Array (frozen variable declarations (readonly, nondeterministic initialization
            | DefineDeclaration (Defines:(IdentifierNextExpressionTuple list)) -> "" // Chapter 2.3.2 DEFINE Declarations p 26
            // TODO | ArrayDefineDeclaration // Chapter 2.3.3 Array Define Declarations p 26-27
            | ConstantsDeclaration (Constants:(Identifier list)) -> "" // Chapter 2.3.4 CONSTANTS Declarations p 27
            | InitConstraint (Expression:SimpleExpression) -> "" // Chapter 2.3.5 INIT Constraint p 27
            | InvarConstraint (Expression:SimpleExpression) -> "" // Chapter 2.3.6 INVAR Constraint p 27
            | TransConstraint (Expression:NextExpression) -> "" // Chapter 2.3.7 TRANS Constraint p 28
            | AssignConstraint (Assigns:(SingleAssignConstraint list)) -> "" // Chapter 2.3.8 ASSIGN Constraint p 28-29
            // TODO | FairnessConstraint // Chapter 2.3.9 FAIRNESS Constraints p 30
            | SpecificationInModule (Specification) -> ""
            // // Chapter 2.3.16 ISA Declarations p 34 (depreciated).Ddon't implement as it is depreciated
            | PredDeclaration (Identifier:Identifier, Expression:SimpleExpression) -> ""// Chapter 2.3.17 PRED and MIRROR Declarations p 34-35. Useful for debugging and CEGAR (Counterexample Guided Abstraction Refinement)
            | MirrorDeclaration (VariableIdentifier:ComplexIdentifier) -> ""


    member this.ExportModuleDeclaration (ModuleDeclaration:ModuleDeclaration) = 
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


    member this.ExportNuXmvProgram (NuXmvProgram:NuXmvProgram) = 
        ""
    (*{ // Chapter 2.3.13 A Program and the main Module p 33
    Modules:ModuleDeclaration list;
    Specifications:Specification list;
}*)

    member this.ExportCtlExpression (ctlExpression:CtlExpression) =
        match ctlExpression with
            | CtlSimpleExpression (Expression:SimpleExpression) -> ""
            | CtlUnaryExpression (Operator:CtlUnaryOperator, Operand:CtlExpression) -> ""
            | CtlBinaryExpression (Left:CtlExpression, Operator:CtlBinaryOperator, Right:CtlExpression) -> ""
            
    member this.ExportLtlExpression (ltlExpression:LtlExpression) =
        match ltlExpression with
            | LtlSimpleExpression (Expression:SimpleExpression) -> ""
            | LtlUnaryExpression (Operator:LtlUnaryOperator,  Operand:LtlExpression) -> ""
            | LtlBinaryExpression (Left:LtlExpression, Operator:LtlBinaryOperator, Right:LtlExpression) -> ""

    member this.ExportSpecification (specification:Specification) =
        match specification with
            | CtlSpecification (CtlExpression:CtlExpression) -> ""
            | LtlSpecification (LtlExpression:LtlExpression) -> ""
        

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