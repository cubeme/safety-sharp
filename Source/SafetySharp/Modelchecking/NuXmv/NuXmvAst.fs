namespace NuXmvDataStructures.Ast

//TODO: For validation active pattern?!?
// interface for validation. 



type Radix = 
    | BinaryRadix
    | OctalRadix
    | DecimalRadix
    | HexadecimalRadix

    
type SignSpecifier =
    | UnsignedSpecifier
    | SignedSpecifier


// Identifier and TypeSpecifier
// Chapter 2 Input Language of NUXMV p 7-8
type Identifier = {
    Name:string;
}
            
// Chapter 2.3.12 References to Module Components (Variables and Defines) p 32-33
// moved it here, because it belongs to the identifier
        
type ComplexIdentifier =
    | NameComplexIdentifier of NameIdentifier:Identifier                                    // NestedComplexIdentifier : Identifier
    | NestedComplexIdentifier of Container:ComplexIdentifier * NameIdentifier:Identifier    // NestedComplexIdentifier : Container '.' NameIdentifier
    | ArrayAccessComplexIdentifier of Container:ComplexIdentifier * Index:SimpleExpression  // NestedComplexIdentifier : Container '[' Index ']'
    | SelfComplexIdentfier
    
//seems to be a duplication of NuXmvType, but isn't:
//The type isn't determined yet. It depends on expressions, which can be contained in a specifier.
type TypeSpecifier =
    | SimpleTypeSpecifier of Specifier:SimpleTypeSpecifier
    | ModuleTypeSpecifier of Specifier:ModuleTypeSpecifier

// Types
        // Chapter 2.1 Types Overview p 8-10
        // The types themselves are only used internally. The declaration of variables
        // in the smv-file may use expression to define e.g. the lower and upper bound 
        // of an array, the number of bytes of a word, etc...

type Type =
    | BooleanType
    | EnumerationType of Domain:(ConstExpression list)
    | UnsignedWordType of Length:int  //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
    | SignedWordType of Length:int    //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
    | IntegerType
    | RealType
    | ArrayType of Lower:int * Upper:int *ElementType:Type
    | SetType //this one is todo

// Note To Type.Settype:
// - Four Different Set Types {BooleanSet,IntegerSet,SymbolicSet,IntegerAndSymbolicSet}
// - Two Constructors: Are created by range (from..to) or by a union of two existing settypes
// => Thus maybe two Subkinds: UnionSetType(properties settype1,settype2) and RangeSetType(properties from,to)


// SimpleTypeSpecifiers
// Note: //TODO: Change following: In the documentation on page 23 only basic_expr is used. But simple_expr would make more sense (no next).
// TODO: Write member GetType, which derives the Type of the TypeSpecifier

type SimpleTypeSpecifier =
    | BooleanTypeSpecifier
    | UnsignedWordTypeSpecifier of Length:BasicExpression  //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
    | SignedWordTypeSpecifier of Length:BasicExpression    //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement
    | RealTypeSpecifier
    | IntegerTypeSpecifier
    | EnumerationTypeSpecifier of Domain:(ConstExpression list) // TODO: "HasSymbolicConstants" and "HasIntegerNumbers" Method, "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum,Integer-Enum}
    | IntegerRangeTypeSpecifier of Lower:BasicExpression * Upper:BasicExpression
    | ArrayTypeSpecifier of Lower:BasicExpression * Upper:BasicExpression *ElementType:SimpleTypeSpecifier


// Chapter 2.2 Expressions p 10-22
// Expressions

type CaseConditionAndEffect = {
    CaseCondition:BasicExpression;
    CaseEffect:BasicExpression;
}

type Expression =
    interface end

type ConstExpression =
    | BooleanConstant of Value:bool
    | SymbolicConstant of SymbolName:Identifier
    | IntegerConstant of Value:System.Numerics.BigInteger
    | RealConstant of Value:float
    | WordConstant of Value:(bool list) * Sign:SignSpecifier * Base:Radix * ImproveReadability:bool
    | RangeConstant of From:System.Numerics.BigInteger * To:System.Numerics.BigInteger

type BasicExpression =
    | ConstExpression of ConstExpression
    | ComplexIdentifierExpression of Identifier:ComplexIdentifier //Identifier is the reference to a variable or a define. Might be hierarchical.
    | UnaryExpression of Operator:UnaryOperator * Operand:BasicExpression
    | BinaryExpression of Left:BasicExpression * Operator:BinaryOperator * Right:BasicExpression
    | TenaryExpression //TODO
    | IndexSubscriptExpression of ExpressionLeadingToArray:BasicExpression * Index:BasicExpression //TODO: Validation, Index has to be word or integer
    | SetExpression of SetBodyExpressions:(BasicExpression list) // TODO there is another way to gain set-expressions by the union-operator. See page 19. Here we use the way by enumerating every possible value
    | CaseExpression of CaseBody:(CaseConditionAndEffect list)
    | BasicNextExpression of Expression:BasicExpression // TODO: Description reads as if argument is a SimpleExpression. Maybe introduce a validator or use simpleexpression. Basically it is also a unary operator, but with different validations

type SimpleExpression = BasicExpression //validation: next forbidden //TODO: Define implicit and explicit convertions, which validate, if conditions in chapter "2.2.4 Simple and Next Expressions" on page 21 are fulfilled. From BasicExpression to SimpleExpression and back again. The conversation step makes the validation
type NextExpression = BasicExpression //validation: next allowed


// Chapter 2.3 Definition of the FSM p 22-35
// FSM


type TypedIdentifier = {
    TypeSpecifier:TypeSpecifier;
    Identifier:Identifier;
}

type SimpleTypedIdentifier = {
    TypeSpecifier:SimpleTypeSpecifier;
    Identifier:Identifier;
}

type IdentifierNextExpressionTuple = {
    Identifier:Identifier;
    Expression:NextExpression;
}

type SingleAssignConstraint = // Chapter 2.3.8 ASSIGN Constraint p 28-29 (for AssignConstraint)
    | CurrentStateAssignConstraint of Identifier:Identifier * Expression:SimpleExpression //Invariant which must evaluate to true. next-Statement is forbidden inside
    | InitialStateAssignConstraint of Identifier:Identifier * Expression:SimpleExpression //Invariant which must evaluate to true. next-Statement is forbidden inside
    | NextStateAssignConstraint of Identifier:Identifier * Expression:NextExpression

type ModuleElement =
    | VarDeclaration of Variables:(TypedIdentifier list) // Chapter 2.3.1 Variable Declarations p 23-26. Type Specifiers are moved into Type-Namespace.
    | IVarDeclaration of InputVariables:(SimpleTypedIdentifier list)
    | FrozenVarDeclaration of FrozenVariables:(SimpleTypedIdentifier list) //Array of frozen variable declarations (readonly, nondeterministic initialization
    | DefineDeclaration of Defines:(IdentifierNextExpressionTuple list) // Chapter 2.3.2 DEFINE Declarations p 26
    // TODO | ArrayDefineDeclaration // Chapter 2.3.3 Array Define Declarations p 26-27
    | ConstantsDeclaration of Constants:(Identifier list) // Chapter 2.3.4 CONSTANTS Declarations p 27
    | InitConstraint of Expression:SimpleExpression // Chapter 2.3.5 INIT Constraint p 27
    | InvarConstraint of Expression:SimpleExpression // Chapter 2.3.6 INVAR Constraint p 27
    | TransConstraint of Expression:NextExpression // Chapter 2.3.7 TRANS Constraint p 28
    | AssignConstraint of Assigns:(SingleAssignConstraint list) // Chapter 2.3.8 ASSIGN Constraint p 28-29
    // TODO | FairnessConstraint // Chapter 2.3.9 FAIRNESS Constraints p 30
    | SpecificationInModule of Specification
    // // Chapter 2.3.16 ISA Declarations p 34 (depreciated).Ddon't implement as it is depreciated
    | PredDeclaration of Identifier:Identifier * Expression:SimpleExpression// Chapter 2.3.17 PRED and MIRROR Declarations p 34-35. Useful for debugging and CEGAR (Counterexample Guided Abstraction Refinement)
    | MirrorDeclaration of VariableIdentifier:ComplexIdentifier


type ModuleDeclaration = { // Chapter 2.3.10 MODULE Declarations p 30-31
    Identifier:Identifier;
    ModuleParameters:Identifier list;
    ModuleElements:ModuleElement list;
 }


type ModuleTypeSpecifier = {// Chapter 2.3.11 MODULE Instantiations p 31.
    ModuleName:Identifier;
    ModuleParameters:BasicExpression list;
}

// Chapter 2.3.12 References to Module Components (Variables and Defines) p 32-33
// moved to the namespace SafetySharp.Modelchecking.NuXmv, because there is also identifier

type NuXmvProgram = { // Chapter 2.3.13 A Program and the main Module p 33
    Modules:ModuleDeclaration list;
    Specifications:Specification list;
}

// Chapter 2.3.14 Namespaces and Constraints on Declarations p 33
// just description
// Chapter 2.3.15 Context p 34
// just description
// chapters 2.3.16 and 2.3.17 mentioned earlier


// Chapter 2.4 Specifications p 35-42
// Specification
            
// Chapter 2.4.1 CTL Specifications p 35-36
type CtlExpression =
    | CtlSimpleExpression of Expression:SimpleExpression
    | CtlUnaryExpression of Operator:CtlUnaryOperator *  Operand:CtlExpression
    | CtlBinaryExpression of Left:CtlExpression * Operator:CtlBinaryOperator * Right:CtlExpression
            
//TODO // Chapter 2.4.2 Invariant Specifications p 36
            
// Chapter 2.4.3 LTL Specifications p 36-38
type LtlExpression =
    | LtlSimpleExpression of Expression:SimpleExpression
    | LtlUnaryExpression of Operator:LtlUnaryOperator *  Operand:LtlExpression
    | LtlBinaryExpression of Left:LtlExpression * Operator:LtlBinaryOperator * Right:LtlExpression

//TODO // Chapter 2.4.4 Real Time CTL Specifications and Computations p 38-39

//TODO // Chapter 2.4.5 PSL Specifications p 39-42


type Specification =
    | CtlSpecification of CtlExpression:CtlExpression
    //TODO: | InvariantSpecification
    | LtlSpecification of LtlExpression:LtlExpression
        
// Chapter 2.5 Variable Order Input p 42-44