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
        of value      : bool *
           sourceInfo : SourceInfo

    /// Represents a positive or negative integer constant such as '-1', '0', or '1'.
    | IntegerLiteral 
        of value      : int *
           sourceInfo : SourceInfo

    /// Represents a positive or negative decimal constant such as '-1.21', '0', or '3.14'.
    | DecimalLiteral 
        of value      : decimal *
           sourceInfo : SourceInfo

    /// Represents an enumeration literal of the form 'EnumType.Literal'. The type slot can be used to retrieve the actual 
    /// declaration of the enumeration from the model's type information table and the literal is represented by its integer
    /// value. The literal's source information, however, maps to the literal's name in the source file.
    | EnumerationLiteral
        of typeSlot          : int *
           typeSourceInfo    : SourceInfo *
           literal           : uint64 *
           literalSourceInfo : SourceInfo

/// Represents a reference to a built-in order user-defined data type.
type TypeReference =
    /// Represents a reference to the built-in Boolean data type.
    | Boolean
        of sourceInfo : SourceInfo

    /// Represents a reference to the built-in integer data type.
    | Integer
        of sourceInfo : SourceInfo

    /// Represents a reference to the built-in decimal data type.
    | Decimal
        of sourceInfo : SourceInfo

    /// Represents a reference to a user-defined tuple type, i.e., a set of unnamed but ordered values, possibly of different types.
    /// Each element of the tuple is a type reference as well, therefore tuple-of-tuples of arbitrary depth are supported.
    | Tuple 
        of dataTypes  : TypeReference list *
           sourceInfo : SourceInfo

    /// Represents a reference to an array, with all elements being of the same type. Arrays are of fixed size, with a length of 'None' 
    /// indicating that the length of the array has not yet been determined.
    | Array
        of dataType   : TypeReference *
           length     : int option *
           sourceInfo : SourceInfo

    /// Represents a reference to a user-defined structure. The slot can be used to retrieve the actual declaration of the struct
    /// from the model's type information table.
    | Struct 
        of slot       : int *
           sourceInfo : SourceInfo

    /// Represents a reference to a user-defined enumeration. The slot can be used to retrieve the actual declaration of the 
    /// enumeration from the model's type information table.
    | Enumeration
        of slot       : int *
           sourceInfo : SourceInfo

/// Represents a side-effect free expression that computes a value.
type Expression =
    /// Represents a constant value in an expression of a certain type.
    | LiteralExpression 
        of literal    : Literal *
           sourceInfo : SourceInfo

    /// Represents the application of an unary operator to a sub-expression.
    | UnaryExpression 
        of operator   : UnaryOperator * 
           expression : Expression *
           sourceInfo : SourceInfo

    /// Represents the application of a binary operator to two sub-expressions.
    | BinaryExpression
        of leftExpression  : Expression * 
           operator        : BinaryOperator * 
           rightExpression : Expression *
           sourceInfo      : SourceInfo

    /// Represents the creation of a tuple.
    | TupleExpression
        of elements    : Expression list *
           sourceInfos : SourceInfo list

/// Represents the declaration of an identifier used to name enumerations, components, fields, methods, and so on.
type Identifier = {
    /// The name of the identifier
    Name : string

    /// The source information of the identifier.
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

    /// The source information of the structure.
    SourceInfo : SourceInfo
}

/// Provides metadata for a local state variable of a component.
type VariableMetadata = 
    /// Defines the range and the overflow behavior of an integer variable.
    | IntegerMetadata
        of min        : int *
           max        : int *
           overflow   : OverflowBehavior

    /// Defines the range, the overflow behavior, and the resolution of a decimal variable.
    | DecimalMetadata
        of min        : decimal *
           max        : decimal *
           overflow   : OverflowBehavior *
           resolution : decimal

type Component = {
    /// The name of the component.
    Name : Identifier

    /// The namespace the component is defined in.
    Namespace : string

    /// The source information of the component.
    SourceInfo : SourceInfo
}

type Interface = {
    /// The name of the interface.
    Name : Identifier

    /// The namespace the interface is defined in.
    Namespace : string

    /// The source information of the interface.
    SourceInfo : SourceInfo
}