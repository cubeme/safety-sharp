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

/// Represents the declaration of an identifier used to name enumerations, components, fields, methods, and so on.
type Identifier = {
    /// The name of the identifier
    Name : string

    /// The source information of the identifier.
    SourceInfo : SourceInfo
}

/// Represents the unary operator of a unary operator expression.
type UnaryOperator =
    /// Represents the unary + operator in an expression such as +x.
    | Plus
    /// Represents the unary - operator in an expression such as -x.
    | Minus
    /// Represents the unary ! operator in an expression such as !b.
    | Negate

/// Represents the binary operator of a binary operator expression.
type BinaryOperator =
    /// Represents the equality operator in an expression such as x == y.
    | Equal
    /// Represents the inequality operator in an expression such as x != y.
    | NotEqual

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

    | Component
        of ComponentSlot : ComponentSlot *
           SourceInfo    : SourceInfo

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

    /// Represents unknown or unsupported type used by simulation-only code.
    | Unknown
        of UnknownType : string *
           SourceInfo  : SourceInfo

/// Represents an expression that computes a value.
type Expression =
    /// Represents a constant value of a certain type.
    | LiteralExpression 
        of Literal    : Literal *
           SourceInfo : SourceInfo

    /// Represents the application of an unary operator to a sub-expression.
    | UnaryOperatorExpression 
        of Operator   : UnaryOperator * 
           Expression : Expression *
           SourceInfo : SourceInfo

    /// Represents the application of a binary operator to two sub-expressions.
    | BinaryOperatorExpression
        of LeftExpression  : Expression * 
           Operator        : BinaryOperator * 
           RightExpression : Expression *
           SourceInfo      : SourceInfo

    | ConditionalExpression
        of Condition       : Expression *
           TrueExpression  : Expression *
           FalseExpression : Expression *
           SourceInfo      : SourceInfo

    | DirectionExpression  // ref, out

    | EmptyExpression
        of SourceInfo : SourceInfo

    | AssignmentExpression
        of LeftExpression  : Expression *
           RightExpression : Expression *
           SourceInfo      : SourceInfo

    | InvocationExpression
        of target     : Expression *
           MethodSlot : MethodSlot *
           Parameters : Expression list *
           SourceInfo : SourceInfo

    | ParameterReferenceExpression
        of parameterSlot : ParameterSlot *
           SourceInfo    : SourceInfo

    | FieldReferenceExpression
        of Target     : Expression *
           FieldSlot  : FieldSlot *
           SourceInfo : SourceInfo

    | PropertyReferenceExpression
        of Target       : Expression *
           PropertySlot : PropertySlot *
           SourceInfo   : SourceInfo

    | VariableReferenceExpression
        of VariableSlot : VariableSlot *
           SourceInfo   : SourceInfo

    | BaseReferenceExpression
        of SourceInfo : SourceInfo

    | ThisReferenceExpression
        of SourceInfo : SourceInfo

    | TypeReferenceExpression
        of Type : TypeReference

    /// Represents the creation of a tuple.
    | TupleExpression
        of Elements   : Expression list *
           SourceInfo : SourceInfo

    | UnknownExpression
        of Expression : obj *
           SourceInfo : SourceInfo

type TypeParameterConstraint =
    | BaseConstraint
    | NewConstraint
    | ClassConstraint
    | StructConstraint

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

type TypeParameterDeclaration = {
    /// The name of the type parameter.
    Name : Identifier

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

    Constraints : TypeParameterConstraint list

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