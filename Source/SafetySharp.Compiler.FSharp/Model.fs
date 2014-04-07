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

namespace SafetySharp.Compiler.Model

open System.Diagnostics
open SafetySharp

// ======================================================================================================================================
// Type Definitions
// ======================================================================================================================================

/// Stores the source information of a model element such as statements, expressions, declarations, and so on.
type SourceInfo = {
    /// The path of the file the model element is declared in.
    File : string

    /// The zero-based index of the line the declaration of the model element begins in.
    BeginLine : int

    /// The zero-based index of the line the declaration of the model element ends in. A value of -1 means unknown.
    EndLine : int

    /// The zero-based index of the column the declaration of the model element begins in.
    BeginColumn : int

    /// The zero-based index of the column the declaration of the model element ends in. A value of -1 means unknown.
    EndColumn : int
}

type TypeInfo = {
    Assembly  : string 
    Namespace : string 
    TypeName  : string 
    HashCode  : int
}

type MemberInfo = {
    TypeInfo   : TypeInfo
    MemberName : string
    HashCode   : int
}

type ComponentSlot = ComponentSlot of TypeInfo
type EnumSlot = EnumSlot of TypeInfo
type EnumMemberSlot = EnumMemberSlot of MemberInfo
type FieldSlot = FieldSlot of MemberInfo
type InterfaceSlot = InterfaceSlot of TypeInfo
type MethodSlot = MethodSlot of MemberInfo
type ParameterSlot = ParameterSlot of int
type PropertySlot = PropertySlot of MemberInfo
type StructSlot = StructSlot of TypeInfo
type VariableSlot = VariableSlot of int
type TypeParameterSlot = TypeParameterSlot of int

/// Represents the declaration of an identifier used to name enumerations, components, fields, methods, and so on.
type Identifier = {
    /// The name of the identifier
    Name : string

    /// The source information of the identifier.
    SourceInfo : SourceInfo
}

/// Represents the unary operator of a unary operator expression.
type UnaryOperator =
    /// Represents the plus operator in an expression such as '+x'.
    | Plus

    /// Represents the minus operator in an expression such as '-x'.
    | Minus

    /// Represents the negation operator in an expression such as '!b'.
    | Negate

/// Represents the binary operator of a binary operator expression.
type BinaryOperator =
    /// Represents the addition operator in an expression such as 'x + y'.
    | Add

    /// Represents the subtraction operator in an expression such as 'x - y'.
    | Subtract

    /// Represents the multiplication operator in an expression such as 'x * y'.
    | Multiply

    /// Represents the division operator in an expression such as 'x / y'.
    | Divide

    /// Represents the modulo operator in an expression such as 'x % y'.
    | Modulus

    /// Represents the Boolean and operator in an expression such as 'x && y'.
    | And

    /// Represents the Boolean or operator in an expression such as 'x || y'.
    | Or

    /// Represents the equality operator in an expression such as 'x == y'
    | Equal

    /// Represents the inequality operator in an expression such as 'x != y'.
    | NotEqual

    /// Represents the greater than operator in an expression such as 'x > y'.
    | Greater

    /// Represents the less than operator in an expression such as 'x < y'.
    | Less

    /// Represents the greater or equal operator in an expression such as 'x >= y'.
    | GreaterEqual

    /// Represents the less or equal operator in an expression such as 'x <= y'.
    | LessEqual

/// Represents a constant value of a certain type.
type Literal =
    /// Represents the Boolean constants 'true' or 'false'.
    | BooleanLiteral 
        of Value      : bool *
           SourceInfo : SourceInfo

    /// Represents a positive or negative integer constant such as '-1', '0', or '1'.
    | IntegerLiteral 
        of Value      : int *
           SourceInfo : SourceInfo

    /// Represents a positive or negative decimal constant such as '-1.21', '0', or '3.14'.
    | DecimalLiteral 
        of Value      : decimal *
           SourceInfo : SourceInfo

    /// Represents an enumeration literal of the form 'EnumType.Literal'. The type slot can be used to retrieve the actual 
    /// declaration of the enumeration from the model's type information table and the literal is represented by its integer
    /// value. The literal's source information, however, maps to the literal's name in the source file.
    | EnumerationLiteral
        of TypeSlot         : EnumSlot *
           TypeSourceInfo   : SourceInfo *
           EnumMember       : EnumMemberSlot *
           MemberSourceInfo : SourceInfo

/// Represents a reference to a built-in or user-defined data type.
type TypeReference =
    /// Represents a reference to the built-in void data type. Can only occur as the return type of a method declaration.
    | Void
        of SourceInfo : SourceInfo

    /// Represents a reference to the built-in Boolean data type.
    | Boolean
        of SourceInfo : SourceInfo

    /// Represents a reference to the built-in integer data type.
    | Integer
        of SourceInfo : SourceInfo

    /// Represents a reference to the built-in decimal data type.
    | Decimal
        of SourceInfo : SourceInfo

    /// Represents a reference to a user-defined tuple type, i.e., a set of unnamed but ordered values, possibly of different types.
    /// Each element of the tuple is a type reference as well, therefore tuple-of-tuples of arbitrary depth are supported.
    | Tuple 
        of DataTypes  : TypeReference list *
           SourceInfo : SourceInfo

    /// Represents a reference to an array, with all elements being of the same type. Arrays are of fixed size, with a length of 'None' 
    /// indicating that the length of the array has not yet been determined.
    | Array
        of DataType   : TypeReference *
           Length     : int option *
           SourceInfo : SourceInfo

    /// Represents a reference to a user-defined structure. The slot can be used to retrieve the actual declaration of the struct
    /// from the model's type information table.
    | Struct 
        of StructSlot : StructSlot *
           SourceInfo : SourceInfo

    /// Represents a reference to a user-defined enumeration. The slot can be used to retrieve the actual declaration of the 
    /// enumeration from the model's type information table.
    | Enum
        of EnumSlot   : EnumSlot *
           SourceInfo : SourceInfo

    /// Represents a reference to a component. The slot can be used to retrieve the actual declaration of the component from the
    /// model's type information table.
    | Component
        of ComponentSlot : ComponentSlot *
           SourceInfo    : SourceInfo

    /// Represents a reference to an interface. The slot can be used to retrieve the actual declaration of the interface from the
    /// model's type information table.
    | Interface
        of InterfaceSlot : InterfaceSlot *
           SourceInfo    : SourceInfo

    | Action
        of TypeParameters : TypeReference list *
           SourceInfo     : SourceInfo

    | Func
        of TypeParameters : TypeReference list *
           ReturnType     : TypeReference *
           SourceInfo     : SourceInfo

    /// Represents a reference to type parameter of a generic interface or component. The slot can be used to retrieve the actual
    /// declaration of the type parameter from the enclosing component's or interface's type parameter table.
    | TypeParameter
        of TypeParameterSlot : TypeParameterSlot *
           SourceInfo        : SourceInfo

    /// Represents unknown or unsupported type used by simulation-only code.
    | Unknown
        of UnknownType : string *
           SourceInfo  : SourceInfo

/// Represents an expression that computes a value.
type Expression =
    /// Represents a constant value of a certain type as an expression.
    | LiteralExpression 
        of Literal    : Literal *
           SourceInfo : SourceInfo

    /// Represents the application of an unary operator to a sub-expression such as 'op e'.
    | UnaryOperatorExpression 
        of Operator   : UnaryOperator * 
           Expression : Expression *
           SourceInfo : SourceInfo

    /// Represents the application of a binary operator to two sub-expressions such as 'e1 op e2'.
    | BinaryOperatorExpression
        of LeftExpression  : Expression * 
           Operator        : BinaryOperator * 
           RightExpression : Expression *
           SourceInfo      : SourceInfo

    /// Represents the application of the ternary conditional operator, such as 'cond ? e1 : e2'.
    | ConditionalExpression
        of Condition       : Expression *
           TrueExpression  : Expression *
           FalseExpression : Expression *
           SourceInfo      : SourceInfo

    (*
    | RefExpression
        of Expression : Expression *
           SourceInfo : SourceInfo

    | OutExpression
        of Expression : Expression *
           SourceInfo : SourceInfo
    *)

    /// Represents an empty expression. Useful, for instance, to represent an empty guard of a transition.
    | EmptyExpression
        of SourceInfo : SourceInfo

    /// Represents the application of the assignment operator on two expressions, such as 'left = right'.
    | AssignmentExpression
        of LeftExpression  : Expression *
           RightExpression : Expression *
           SourceInfo      : SourceInfo

    /// Represents the invocation of a function or method on a target expression such as 'target.method(params)'. The method
    /// slot can be used to retrieve the actual declaration of the method from the model's method information table.
    | InvocationExpression
        of target     : Expression *
           MethodSlot : MethodSlot *
           Parameters : Expression list *
           SourceInfo : SourceInfo

    /// Represents a reference to a method parameter. The parameter slot can be used to retrieve the actual declaration of the
    /// parameter from the enclosing method's parameter table.
    | ParameterReferenceExpression
        of parameterSlot : ParameterSlot *
           SourceInfo    : SourceInfo

    /// Represents a reference to a field of a target object such as 'target.field'. The field slot can be used to retrieve
    /// the actual declaration of the field from the model's field information table.
    | FieldReferenceExpression
        of Target     : Expression *
           FieldSlot  : FieldSlot *
           SourceInfo : SourceInfo

    /// Represents a reference to a property of a target object such as 'target.Property'. The property slot can be used to 
    /// retrieve the actual declaration of the property from the model's property information table.
    | PropertyReferenceExpression
        of Target       : Expression *
           PropertySlot : PropertySlot *
           SourceInfo   : SourceInfo

    /// Represents a reference to a locally defined variable of the enclosing method. The variable slot can be used to retrieve 
    /// the actual declaration of the variable from the enclosing method's variable table.
    | VariableReferenceExpression
        of VariableSlot : VariableSlot *
           SourceInfo   : SourceInfo

    /// Represents a reference to the base of the component that is currently executing this expression.
    | BaseReferenceExpression
        of SourceInfo : SourceInfo

    /// Represents a reference to the component that is currently executing this expression.
    | ThisReferenceExpression
        of SourceInfo : SourceInfo

    /// Represents a reference to a type as an expression.
    | TypeReferenceExpression
        of Type : TypeReference

    /// Represents the creation of a tuple.
    | TupleExpression
        of Elements   : Expression list *
           SourceInfo : SourceInfo

    /// Represents an unknown expression that is either not supported (used in simulation mode only) or contains syntactic or 
    /// semantic errors.
    | UnknownExpression
        of Expression : obj *
           SourceInfo : SourceInfo

/// Represents a statement.
type Statement =
    | BlockStatement
        of Statements : Statement list *
           SourceInfo : SourceInfo

    | EmptyStatement
        of SourceInfo : SourceInfo

    | ExpressionStatement
        of Expression : Expression *
           SourceInfo : SourceInfo

    | IfElseStatement
        of Condition      : Expression *
           TrueStatement  : Statement *
           FalseStatement : Statement *
           SourceInfo     : SourceInfo

    | ReturnStatement
        of Expression : Expression *
           SourceInfo : SourceInfo

    | VariableDeclarationStatement
        of Type        : TypeReference *
           Name        : Identifier *
           Initializer : Expression *
           SourceInfo  : SourceInfo

    | UnknownStatement
        of Statement  : obj *
           SourceInfo : SourceInfo

/// Represents a parameter of a method declaration.
type ParameterDeclaration = {
    /// The name of the parameter.
    Name : Identifier

    /// The type of the parameter.
    Type : TypeReference

    /// The source information of the parameter.
    SourceInfo : SourceInfo
}

type PortType =
    | Required
    | Provided

type Priority = {
    Priority : int
    SourceInfo : SourceInfo
}

/// Represents a method declaration or operator declaration of a user-defined immutable structure or a component.
type MethodDeclaration = {
    /// The name of the method.
    Name : Identifier

    /// The parameters of the method.
    Parameters : ParameterDeclaration list

    /// The return type of the method.
    ReturnType : TypeReference

    /// The method's implementation.
    Statement : Statement

    IsOutport : bool

    Priority : Priority

    /// The source information of the method.
    SourceInfo : SourceInfo
}

/// Represents the declaration of a user-defined enumeration.
type EnumDeclaration = {
    /// The name of the enumeration.
    Name : Identifier

    /// The namespace the enumeration is defined in.
    Namespace : string

    /// The members declared by the enumeration.
    Members : Identifier list

    /// The source information of the enumeration.
    SourceInfo : SourceInfo
}

/// Represents the declaration of a user-defined immutable structure.
type StructDeclaration = {
    /// The name of the structure.
    Name : Identifier

    /// The namespace the structure is defined in.
    Namespace : string

    /// The types of the structure's fields.
    FieldTypes : TypeReference list

    /// The names of the structure's fields.
    FieldNames : Identifier list

    /// The methods defined by the structure. The method slots can be used to retrieve the actual method declarations from 
    /// the model's method information table.
    Methods : MethodSlot list

    /// The source information of the structure.
    SourceInfo : SourceInfo
}

type FieldDeclaration = {
    /// The name of the field.
    Name : Identifier

    /// The type of the field.
    Type : TypeReference

    /// The source information of the field.
    SourceInfo : SourceInfo
}

type PropertyDeclaration = {
    /// The name of the property.
    Name : Identifier

    /// The type of the property.
    Type : TypeReference

    Getter : Statement

    Setter : Statement

    PortType : PortType option

    Priority : Priority

    /// The source information of the property.
    SourceInfo : SourceInfo
}

type TypeParameterConstraint =
    | BaseConstraint
    | NewConstraint
    | ClassConstraint
    | StructConstraint

type TypeParameterDeclaration = {
    /// The name of the type parameter.
    Name : Identifier

    /// The contraints of the type parameter.
    Constraint : TypeParameterConstraint list

     /// The source information of the type parameter.
    SourceInfo : SourceInfo
}

type FaultDeclaration = {
    /// The name of the fault.
    Name : Identifier

    /// The namespace the fault is defined in.
    Namespace : string

    Occurrence : TypeReference

    Properties : PropertySlot list

    Methods : MethodSlot list

    Fields : FieldSlot list

    /// The source information of the fault.
    SourceInfo : SourceInfo
}

type ComponentType = 
    | Sensor
    | Actuator
    | Controller
    | Environment
    | Untyped

type State = {
    EnumType : EnumSlot
    EnumMember : EnumMemberSlot

    EntryAction : Statement
    ExitAction : Statement
    DoAction : Statement
}

type TransitionDeclaration = {
    Source : State
    Target : State
    Guard : Expression
    Action : Statement

    Priority : Priority

    Identifier : Identifier
    
    SourceInfo : SourceInfo
}

type StateMachine = {
    Transitions : TransitionDeclaration list
    States : State list
}

type ComponentDeclaration = {
    /// The name of the component.
    Name : Identifier

    /// The namespace the component is defined in.
    Namespace : string

    Type : ComponentType

    Properties : PropertySlot list

    Methods : MethodSlot list

    Fields : FieldSlot list

    TypeParameter : TypeParameterDeclaration list

    Base : TypeReference

    Interfaces : TypeReference list

    StateMachine : StateMachine option

    /// The source information of the component.
    SourceInfo : SourceInfo
}

type InterfaceDeclaration = {
    /// The name of the interface.
    Name : Identifier

    /// The namespace the interface is defined in.
    Namespace : string

    Properties : PropertySlot list

    Methods : MethodSlot list

    TypeParameter : TypeParameterDeclaration list

    Interfaces : TypeReference list

    /// The source information of the interface.
    SourceInfo : SourceInfo
}

type PartitionDeclaration = {
    Component : ComponentSlot
}

type ModelConfiguration = {
    Name : Identifier

    Partitions : PartitionDeclaration list
}

// -----------------------------------------------------
// Instance model

/// Provides metadata for a local state variable of a component.
type VariableMetadata = 
    /// Defines the range and the overflow behavior of an integer variable.
    | IntegerMetadata
        of Min        : int *
           Max        : int *
           Overflow   : OverflowBehavior

    /// Defines the range, the overflow behavior, and the resolution of a decimal variable.
    | DecimalMetadata
        of Min        : decimal *
           Max        : decimal *
           Overflow   : OverflowBehavior *
           Resolution : decimal


type TypeTables = {
    Components : Map<ComponentSlot, ComponentDeclaration>
}
//
//module T =
//    let getComponent tt (ComponentSlot s) = 
//        tt.Components.[s]