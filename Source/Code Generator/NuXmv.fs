﻿// The MIT License (MIT)
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


// AST of a subset of NuXmv. NuXmv syntax is a superset of NuSMV syntax
// Source of AST: NuXmv User Manual V. 1.0

module NuXmvGenerator

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading
open Generator

let elements = [
    {
        // Chapter 2 Input Language of NUXMV p 7-8
        Name = "SafetySharp.Modelchecking.NuXmv"
        Classes =
        [
            {   
                Name = "Identifier"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the identifier."
                        CanBeNull = false
                    }
                ]
            }
            // Chapter 2.3.12 References to Module Components (Variables and Defines) p 32-33
            // moved it here, because it belongs to the identifier
            {   
                Name = "ComplexIdentifier"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "IdentifierComplexIdentifier" // NestedComplexIdentifier	: Identifier
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The identifier which references a variable or the name of a container/self."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "NestedComplexIdentifier" // NestedComplexIdentifier	: [ Container '.' ] Identifier
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Container"
                        Type = "ComplexIdentifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Identifier (and maybe the Index) reference a struct. This references a specific member in this struct."
                        CanBeNull = true
                    }
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The identifier which definitively references a variable."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ArrayAccessComplexIdentifier" // NestedComplexIdentifier	:  Container [ '[' Index ']' ]
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Container"
                        Type = "ComplexIdentifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Identifier (and maybe the Index) reference a struct. This references a specific member in this struct."
                        CanBeNull = true
                    }
                    {
                        Name = "Index"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Container references an array. This is the index of a specific element in this array."
                        CanBeNull = true
                    }
                ]
            }
            {   
                Name = "SelfComplexIdentifier"
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "NuXmvType"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                //seems to be a duplication of NuXmvType, but isn't:
                //The type isn't determined yet. It depends on expressions, which can be contained in a specifier.
                Name = "NuXmvTypeSpecifier"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
        ]
    }
    {
        // Chapter 2.1 Types Overview p 8-10
        // The types themselves are only used internally. The declaration of variables
        // in the smv-file may use expression to define e.g. the lower and upper bound 
        // of an array, the number of bytes of a word, etc...
        Name = "SafetySharp.Modelchecking.NuXmv.Types"
        Classes = 
        [
            {
                Name = "BooleanType"
                Base = "NuXmvType"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "EnumerationType"
                Base = "NuXmvType"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Domain"
                        Type = "ConstExpression"
                        CollectionType = Array
                        Validation = None
                        Comment = "Possible values of the Enumeration Type."
                        CanBeNull = false
                    }
                    //    TODO: "HasSymbolicConstants" and "HasIntegerNumbers" as methods in partial class
                    //          Method "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum,Integer-Enum}
                ]
            }            
            {   
                Name = "WordType"
                Base = "NuXmvType"
                IsAbstract = true
                Properties = 
                [
                    {
                        Name = "Length"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Length of the word."
                        CanBeNull = false
                    }
                ]
            }          
            {   
                Name = "UnsignedWordType"
                Base = "WordType"
                IsAbstract = false
                Properties = []
            }          
            {   
                Name = "SignedWordType"
                Base = "WordType"
                IsAbstract = false
                Properties = []
            } //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement            
            {
                Name = "IntegerType"
                Base = "NuXmvType"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "RealType"
                Base = "NuXmvType"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "ArrayType"
                Base = "NuXmvType"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Lower"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Upper bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "ElementType"
                        Type = "NuXmvType"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Type of the elements of the array."
                        CanBeNull = false
                    }
                ]
            }            
            {
                // This one is a TODO
                // - Four Different Set Types {BooleanSet,IntegerSet,SymbolicSet,IntegerAndSymbolicSet}
                // - Two Constructors: Are created by range (from..to) or by a union of two existing settypes
                // => Thus maybe two Subkinds: UnionSetType(properties settype1,settype2) and RangeSetType(properties from,to)
                Name = "SetType"
                Base = "NuXmvType"
                IsAbstract = true
                Properties = []   
            }
        ]
    }
    {
        // Chapter 2.3.1 Variable Declarations -> Type Specifiers p 23
        Name = "SafetySharp.Modelchecking.NuXmv.SimpleTypeSpecifiers"
        Classes = 
        [
                  
            {   
                Name = "NuXmvSimpleTypeSpecifier"
                Base = "NuXmvTypeSpecifier"
                IsAbstract = true
                Properties = 
                [
                    //TODO
                    (*{
                        Name = "Type"
                        Type = "NuXmvType"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "Type of SimpleTypeSpecifier. No data. Should be evaluated."
                        CanBeNull = false
                    }*)
                ]
            }
            {
                Name = "BooleanTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "WordTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = true
                Properties = 
                [
                    {
                        Name = "Length"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Length of the word."
                        CanBeNull = false
                    }
                ]
            }          
            {   
                Name = "UnsignedWordTypeSpecifier"
                Base = "WordTypeSpecifier"
                IsAbstract = false
                Properties = []
            }          
            {   
                Name = "SignedWordTypeSpecifier"
                Base = "WordTypeSpecifier"
                IsAbstract = false
                Properties = []
            } //in two's complement: See wikipedia http://en.wikipedia.org/wiki/Two's_complement            
            {
                Name = "RealTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "IntegerTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = false
                Properties = []
            }            
            {
                Name = "EnumerationTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Domain"
                        Type = "ConstExpression"
                        CollectionType = Array
                        Validation = None
                        Comment = "Possible values of the Enumeration Type."
                        CanBeNull = false
                    }
                    //    TODO: "HasSymbolicConstants" and "HasIntegerNumbers" as methods in partial class
                    //          Method "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum,Integer-Enum}
                ]
            }            
            {
                Name = "ArrayTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Lower"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Upper bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "ElementTypeSpecifier"
                        Type = "NuXmvSimpleTypeSpecifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Type of the elements of the array."
                        CanBeNull = false
                    }
                ]
            }             
            {
                Name = "IntegerRangeTypeSpecifier"
                Base = "NuXmvSimpleTypeSpecifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Lower"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Upper bound of the array."
                        CanBeNull = false
                    }
                ]
            }

        ]
    }
    {
        // Chapter 2.2 Expressions p 10-22
        Name = "SafetySharp.Modelchecking.NuXmv.Expressions"
        Classes = 
        [
            {   
                Name = "Expression" //inherited by BasicExpression (also called next expression) and SimpleExpression (which nests BasicExpression and dynamically forbids NextExpressions)
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "BasicExpression" //also called next expression
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "ConstExpression"
                Base = "BasicExpression"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "BooleanLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "bool"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The Boolean value of the expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "SymbolicLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The string containing the element name of an enum."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "IntegerLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "System.Numerics.BigInteger"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The integer value of an expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "RealLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "float"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The float value of an expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "WordLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = "System.Collections.BitArray"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The bit value of a word expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Type"
                        Type = "WordType"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The float value of an expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Radix"
                        Type = "NuXmvRadix"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Radix of Numeral System (binary, octal, decimal or hexadecimal)."
                        CanBeNull = false
                    }
                    {
                        Name = "SignSpecifier"
                        Type = "NuXmvSignSpecifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Specifies, whether signed or unsigned."
                        CanBeNull = false
                    }                    
                    {
                        Name = "ImproveReadability"
                        Type = "bool"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "If true underscore is placed every 3 digits to improve readability."
                        CanBeNull = false
                    }
                ]
            }            
            {
                Name = "RangeLiteral"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "From"
                        Type = "System.Numerics.BigInteger"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The value the range starts with (inclusive)."
                        CanBeNull = false
                    }
                    {
                        Name = "To"
                        Type = "System.Numerics.BigInteger"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The value the range ends with (inclusive)."
                        CanBeNull = false
                    }
                ]
            }
            (*
            {   
                Name = "BasicExpression" //TODO
                Base = "Expression"
                IsAbstract = true
                Properties = []
            }
            *)                    
            {   
                // The expression which references a variable.
                // Note: All identifiers (variables, defines, symbolic constants, etc) can be used prior to their definition
                Name = "VariableIdentifier" //TODO
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the identifier which references a variable."
                        CanBeNull = false
                    }
                ]
            }                   
            {   
                //The expression which references a Define.
                Name = "DefineIdentifier" //TODO
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the identifier which references a variable."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "BinaryExpression"
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "NuXmvBinaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                Name = "UnaryExpression"
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "NuXmvUnaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                        CanBeNull = false
                    }
                ]
            }                     
            {
                Name = "IndexSubscriptExpression"
                Base = "BasicExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "ExpressionLeadingToArray"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The expression leading to the array we index."
                        CanBeNull = false
                    }
                    {
                        //TODO:
                        Name = "Index"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The index"
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "SetExpression" //TODO            
                Base = "BasicExpression"
                IsAbstract = false
                Properties = []
            }       
            {
                Name = "CaseExpression" //TODO            
                Base = "BasicExpression"
                IsAbstract = false
                Properties = []
            }       
            {
                Name = "BasicNextExpression" //TODO            
                Base = "BasicExpression"
                IsAbstract = false
                Properties = []
            }      
            {
                Name = "SimpleExpression" //TODO: Define implicit and explicit convertions, which validate, if conditions in chapter "2.2.4 Simple and Next Expressions" on page 21 are fulfilled. From BasicExpression to SimpleExpression and back again. The conversation step makes the validation
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "NestedExpression"
                        Type = "BasicExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The actual expression"
                        CanBeNull = false
                    }                    
                ]
            }      
        ]
    }
    {
        // Chapter 2.3 Definition of the FSM p 22-35
        Name = "SafetySharp.Modelchecking.NuXmv.FSM" //or maybe better Module
        Classes =
        [
            {
                Name = "ModuleElement"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = []
            }                    

            // Chapter 2.3.1 Variable Declarations p 23-26. Type Specifiers are moved into Type-Namespace.
            {
                Name = "TypedIdentifier"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "TypeSpecifier"
                        Type = "NuXmvTypeSpecifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The typespecifier of the tuple which is mainly used in the variable declaration part of a module."
                        CanBeNull = false
                    }
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The identifier of the tuple which is mainly used in the variable declaration part of a module."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "SimpleTypedIdentifier"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "TypeSpecifier"
                        Type = "NuXmvSimpleTypeSpecifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The typespecifier of the tuple which is mainly used in the variable declaration part of a module."
                        CanBeNull = false
                    }
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The identifier of the tuple which is mainly used in the variable declaration part of a module."
                        CanBeNull = false
                    }
                ]
            }  
            {
                Name = "VarDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Variables"
                        Type = "TypedIdentifier"
                        CollectionType = Array
                        Validation = None
                        Comment = "Array of variable declarations"
                        CanBeNull = false
                    }                    
                ]
            }    
            {
                Name = "IvarDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "InputVariables"
                        Type = "SimpleTypedIdentifier"
                        CollectionType = Array
                        Validation = None
                        Comment = "Array of input variable declarations"
                        CanBeNull = false
                    }                    
                ]
            }      
            {
                Name = "FrozenVarDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "FrozenVariables"
                        Type = "SimpleTypedIdentifier"
                        CollectionType = Array
                        Validation = None
                        Comment = "Array of frozen variable declarations (readonly, nondeterministic initialization)"
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.2 DEFINE Declarations p 26
            {
                Name = "IdentifierExpressionTuple"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "Expression"
                        Type = "BasicExpression" //Next allowed
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "DefineDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Defines"
                        Type = "IdentifierExpressionTuple"
                        CollectionType = Array
                        Validation = None
                        Comment = "Array of variable declarations"
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.3 Array Define Declarations p 26-27
            // TODO
            // Chapter 2.3.4 CONSTANTS Declarations p 27
            {
                Name = "ConstantsDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Constants"
                        Type = "Identifier"
                        CollectionType = Array
                        Validation = None
                        Comment = "Array of identifiers of constants."
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.5 INIT Constraint p 27
            {
                Name = "InitConstraint"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "SimpleExpression" //next forbidden
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Initial Condition which must evaluate to true. next-Statement is forbidden inside."
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.6 INVAR Constraint p 27
            {
                Name = "InvarConstraint"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "SimpleExpression" //next forbidden
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Invariant which must evaluate to true. next-Statement is forbidden inside."
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.7 TRANS Constraint p 28
            {
                Name = "TransConstraint"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "BasicExpression" //next allowed
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Invariant which must evaluate to true. next-Statement is allowed inside."
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.8 ASSIGN Constraint p 28-29
            {
                Name = "SingleAssignConstraint"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties =  
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "CurrentStateAssignConstraint"
                Base = "SingleAssignConstraint"
                IsAbstract = false
                Properties =  
                [
                    {
                        Name = "Expression"
                        Type = "SimpleExpression" //next forbidden
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Invariant which must evaluate to true. next-Statement is forbidden inside."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "InitialStateAssignConstraint"
                Base = "SingleAssignConstraint"
                IsAbstract = false
                Properties =  
                [
                    {
                        Name = "Expression"
                        Type = "SimpleExpression" //next forbidden
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Invariant which must evaluate to true. next-Statement is forbidden inside."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "NextStateAssignConstraint"
                Base = "SingleAssignConstraint"
                IsAbstract = false
                Properties =  
                [
                    {
                        Name = "Expression"
                        Type = "BasicExpression" //next allowed
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Invariant which must evaluate to true. next-Statement is allowed inside."
                        CanBeNull = false
                    }                    
                ]
            }
            {
                Name = "AssignConstraint"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Assigns"
                        Type = "SingleAssignConstraint"
                        CollectionType = Array
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }                    
                ]
            }
            // Chapter 2.3.9 FAIRNESS Constraints p 30
            // TODO
            // Chapter 2.3.10 MODULE Declarations p 30-31            
            {   
                Name = "ModuleDeclaration"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "ModuleParameters"
                        Type = "Identifier"
                        CollectionType = Array
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "ModuleElements"
                        Type = "ModuleElement"
                        CollectionType = Array
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                ]
            }
            // Chapter 2.3.11 MODULE Instantiations p 31. TODO: Maybe move into Type-Namespace or make a TypeSpecifier-Namespace
            {   
                Name = "NuXmvModuleTypeSpecifier"
                Base = "NuXmvTypeSpecifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "ModuleName"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "ModuleParameters"
                        Type = "BasicExpression" //next allowed
                        CollectionType = Array
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                ]
            }
            // Chapter 2.3.12 References to Module Components (Variables and Defines) p 32-33
            // moved to the namespace SafetySharp.Modelchecking.NuXmv, because there is also identifier

            // Chapter 2.3.13 A Program and the main Module p 33
            {   
                Name = "NuXmvProgram"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Modules"
                        Type = "ModuleDeclaration"
                        CollectionType = Array
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                ]
            }
            // Chapter 2.3.14 Namespaces and Constraints on Declarations p 33
            // just description
            // Chapter 2.3.15 Context p 34
            // just description
            // Chapter 2.3.16 ISA Declarations p 34 (depreciated)
            // don't implement as it is depreciated
            // Chapter 2.3.17 PRED and MIRROR Declarations p 34-35
            //TODO: Useful for debugging and CEGAR (Counterexample Guided Abstraction Refinement)
            {
                Name = "PredDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = true
                    }    
                    {
                        Name = "Expression"
                        Type = "SimpleExpression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }                    
                ]
            }
            {
                Name = "MirrorDeclaration"
                Base = "ModuleElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "VariableIdentifier"
                        Type = "ComplexIdentifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }                    
                ]
            }
        ]
    }
    {
        // Chapter 2.4 Specifications p 35-42
        Name = "SafetySharp.Modelchecking.NuXmv.Specification"
        Classes =
        [
            // Chapter 2.4.1 CTL Specifications p 35-36
            {   
                Name = "CtlExpression"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "CtlSimpleExpression"
                Base = "CtlExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "SimpleExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The simple expression without a next."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "CtlBinaryExpression"
                Base = "CtlExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "CtlExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "NuXmvCtlBinaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "CtlExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                Name = "CtlUnaryExpression"
                Base = "CtlExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "CtlExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "NuXmvCtlUnaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                        CanBeNull = false
                    }
                ]
            }
            (*{   
                Name = "Identifier"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the identifier."
                        CanBeNull = false
                    }
                ]
            }*)
            // Chapter 2.4.2 Invariant Specifications p 36
            //TODO
            // Chapter 2.4.3 LTL Specifications p 36-38
            {   
                Name = "LtlExpression"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "LtlSimpleExpression"
                Base = "LtlExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "SimpleExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The simple expression without a next."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "LtlBinaryExpression"
                Base = "LtlExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "LtlExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "NuXmvLtlBinaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "LtlExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                Name = "LtlUnaryExpression"
                Base = "LtlExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "LtlExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "NuXmvLtlUnaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                        CanBeNull = false
                    }
                ]
            }
            // Chapter 2.4.4 Real Time CTL Specifications and Computations p 38-39
            //TODO
            // Chapter 2.4.5 PSL Specifications p 39-42
            //TODO
        ]
    }

    
    // Chapter 2.5 Variable Order Input p 42-44
    
    
]

let Generate outputFile =
    generateCode {
        Elements = elements
        OutputFile = outputFile
        BaseClass = "NuXmvElement"
        VisitorName = "NuXmvVisitor"
        RewriterName = "NuXmvRewriter"
        Namespace = "SafetySharp.Modelchecking.NuXmv"
        Visibility = Internal
    }

