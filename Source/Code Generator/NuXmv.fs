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


// AST of a subset of NuXmv. NuXmv syntax is a superset of NuSMV syntax
// Source of AST: NuXmv User Manual V. 1.0

//TODO: Check validations

//TODO: Maybe remove SimpleExpression and Replace every use by a custom validation
//      Maybe add NotImplementedYet-Exception to generated Visitor

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
            // TODO: Write validator, which checks, if string is not a keyword and follows all rules
            // TODO: Alow Generator to define custom validation functions
            {   
                Name = "Identifier"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = Singleton "string"
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
                Name = "NameComplexIdentifier" // NestedComplexIdentifier : Identifier
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "NameIdentifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "The identifier which references a variable or the name of a container (if part of a nested identifier)."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "NestedComplexIdentifier" // NestedComplexIdentifier : Container '.' NameIdentifier
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Container"
                        Type = Singleton "ComplexIdentifier"
                        Validation = NotNull
                        Comment = "Identifier (and maybe the Index) reference a struct. This references a specific member in a module. (Syntax: Container '.' NameIdentifier)"
                        CanBeNull = false
                    }
                    {
                        Name = "NameIdentifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "The identifier which references a specific member in a module.  (Syntax: Container '.' NameIdentifier)"
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ArrayAccessComplexIdentifier" // NestedComplexIdentifier : Container '[' Index ']'
                Base = "ComplexIdentifier"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Container"
                        Type = Singleton "ComplexIdentifier"
                        Validation = NotNull
                        Comment = "This references a specific member in this struct."
                        CanBeNull = false
                    }
                    {
                        Name = "Index"
                        Type = Singleton "SimpleExpression"
                        Validation = NotNull
                        Comment = "Container references an array. This is the index of a specific element in this array."
                        CanBeNull = false
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
                Name = "NuXmvType" //can't be renamed to Type because System.Type exists
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                //seems to be a duplication of NuXmvType, but isn't:
                //The type isn't determined yet. It depends on expressions, which can be contained in a specifier.
                Name = "NuXmvTypeSpecifier" //called NuXmvTypeSpecifier to be consistent with NuXmvType
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
                        Type = Array "ConstExpression"
                        Validation = None
                        Comment = "Possible values of the Enumeration Type."
                        CanBeNull = false
                    }
                    //    TODO: "HasSymbolicConstants" and "HasIntegerNumbers" as methods in partial class
                    //          Method "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum)} (No Integer-Enum, because "In the NUXMV type system an expression of the type integer enum is always converted to the type integer")
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
                        Type = Singleton "int"
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
                        Type = Singleton "int"
                        Validation = None //No validation because of value type int
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = Singleton "int"
                        Validation = None //No validation because of value type int
                        Comment = "Upper bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "ElementType"
                        Type = Singleton "NuXmvType"
                        Validation = NotNull
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
            //TODO: Change following: In the documentation on page 23 only basic_expr is used. But simple_expr would make more sense (no next).
            {   
                // TODO: Write member GetNuXmvType, which derives the NuXmvType of the TypeSpecifier
                Name = "NuXmvSimpleTypeSpecifier"
                Base = "NuXmvTypeSpecifier"
                IsAbstract = true
                Properties = []
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
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
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
                        Type = Array "ConstExpression"
                        Validation = None //ImmutableArrays aren't validated
                        Comment = "Possible values of the Enumeration Type."
                        CanBeNull = false
                    }
                    //    TODO: "HasSymbolicConstants" and "HasIntegerNumbers" as methods in partial class
                    //          Method "GetEnumerationType -> {SymbolicEnum, Integer-And-Symbolic-Enum,Integer-Enum}
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
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "Upper bound of the array."
                        CanBeNull = false
                    }
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
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "Upper bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "ElementTypeSpecifier"
                        Type = Singleton "NuXmvSimpleTypeSpecifier"
                        Validation = NotNull
                        Comment = "Type of the elements of the array."
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
                Name = "BooleanConstant"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = Singleton "bool"
                        Validation = None
                        Comment = "The Boolean value of the expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "SymbolicConstant"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "An identifier containing the element name of an enum."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "IntegerConstant"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    //TODO: Additional constructor for int
                    {
                        Name = "Value"
                        Type = Singleton "System.Numerics.BigInteger" //is value type => no validation
                        Validation = None
                        Comment = "The integer value of an expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "RealConstant"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    //TODO: Member: Representation (float, fractional or exponential)
                    {
                        Name = "Value"
                        Type = Singleton "float"
                        Validation = None
                        Comment = "The float value of an expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "WordConstant"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    //TODO: Write Member-Function, which extracts the word with (which is defined in "Value" inside the BitArray)
                    //TODO: Write additional constructors, which allow to enter a value and the width of the BitArray
                    {
                        Name = "Value"
                        Type = Singleton "bool[]" // I am quite surprised: is a reference type
                        Validation = NotNull
                        Comment = "The bit value of a word expression."
                        CanBeNull = false
                    }
                    {
                        Name = "SignSpecifier"
                        Type = Singleton "NuXmvSignSpecifier"
                        Validation = InRange
                        Comment = "Specifies, whether signed or unsigned."
                        CanBeNull = false
                    }        
                    {
                        Name = "Base"
                        Type = Singleton "NuXmvRadix"
                        Validation = InRange
                        Comment = "Radix of Numeral System (binary, octal, decimal or hexadecimal)."
                        CanBeNull = false
                    }       
                    {
                        Name = "ImproveReadability"
                        Type = Singleton "bool"
                        Validation = None
                        Comment = "If true underscore is placed every 3 or 4 digits to improve readability."
                        CanBeNull = false
                    }
                ]
            }            
            {
                Name = "RangeConstant"
                Base = "ConstExpression"
                IsAbstract = false
                Properties =
                [
                    // write additional constructor, which allows to enter int-Values
                    {
                        Name = "From"
                        Type = Singleton "System.Numerics.BigInteger"
                        Validation = None
                        Comment = "The value the range starts with (inclusive)."
                        CanBeNull = false
                    }
                    {
                        Name = "To"
                        Type = Singleton "System.Numerics.BigInteger"
                        Validation = None
                        Comment = "The value the range ends with (inclusive)."
                        CanBeNull = false
                    }
                ]
            }         
            {   
                // The expression which references a variable or a define.
                // Note: All identifiers (variables, defines, symbolic constants, etc) can be used prior to their definition
                Name = "ComplexIdentifierExpression"
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "ComplexIdentifier"
                        Validation = NotNull
                        Comment = "The reference to a variable or a define. Might be hierarchical."
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
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "NuXmvUnaryOperator"
                        Validation = InRange
                        Comment = "The operator of the unary expression."
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
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "NuXmvBinaryOperator"
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                //TODO
                Name = "TenaryExpression"
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    (*{
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
                    }*)
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
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "The expression leading to the array we index."
                        CanBeNull = false
                    }
                    {
                        //TODO: Validation: Index has to be word or integer
                        Name = "Index"
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "The index"
                        CanBeNull = false
                    }
                ]
            }
            {
                // TODO there is another way to gain set-expressions by the union-operator. See page 19:
                // Here we use the way by enumerating every possible value
                Name = "SetExpression"             
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "SetBodyExpression"
                        Type = Array "BasicExpression"
                        Validation = None
                        Comment = "The members in the set expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "CaseConditionAndEffect"
                Base = "NuXmvElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "CaseCondition"
                        Type = Singleton "BasicExpression"
                        Validation = None
                        Comment = "Left side of the ':' in a case expression."
                        CanBeNull = false
                    }
                    {
                        Name = "CaseEffect"
                        Type = Singleton "BasicExpression"
                        Validation = None
                        Comment = "Right side of the ':' in a case expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "CaseExpression"
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "CaseBody"
                        Type = Array "CaseConditionAndEffect"
                        Validation = None
                        Comment = "The members in the case expression."
                        CanBeNull = false
                    }
                ]
            }       
            {
                // TODO: Description reads as if argument is a SimpleExpression. Maybe introduce a validator or use simpleexpression.
                // basically it is also a unary operator, but with different validations
                Name = "BasicNextExpression" 
                Base = "BasicExpression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
                        Comment = "The expression of the basic next expression."
                        CanBeNull = false
                    }
                ]
            }

            //TODO: Maybe remove and replace by a validation everywhere
            {
                Name = "SimpleExpression" //TODO: Define implicit and explicit convertions, which validate, if conditions in chapter "2.2.4 Simple and Next Expressions" on page 21 are fulfilled. From BasicExpression to SimpleExpression and back again. The conversation step makes the validation
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "NestedExpression"
                        Type = Singleton "BasicExpression"
                        Validation = NotNull
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
                IsAbstract = true
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
                        Type = Singleton "NuXmvTypeSpecifier"
                        Validation = NotNull
                        Comment = "The typespecifier of the tuple which is mainly used in the variable declaration part of a module."
                        CanBeNull = false
                    }
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
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
                        Type = Singleton "NuXmvSimpleTypeSpecifier"
                        Validation = NotNull
                        Comment = "The typespecifier of the tuple which is mainly used in the variable declaration part of a module."
                        CanBeNull = false
                    }
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
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
                        Type = Array "TypedIdentifier"
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
                        Type = Array "SimpleTypedIdentifier"
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
                        Type = Array "SimpleTypedIdentifier"
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
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "Expression"
                        Type = Singleton "BasicExpression" //Next allowed
                        Validation = NotNull
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
                        Type = Array "IdentifierExpressionTuple"
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
                        Type = Array "Identifier"
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
                        Type = Singleton "SimpleExpression" //next forbidden
                        Validation = NotNull
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
                        Type = Singleton "SimpleExpression" //next forbidden
                        Validation = NotNull
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
                        Type = Singleton "BasicExpression" //next allowed
                        Validation = NotNull
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
                        Type = Singleton "Identifier"
                        Validation = NotNull
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
                        Type = Singleton "SimpleExpression" //next forbidden
                        Validation = NotNull
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
                        Type = Singleton "SimpleExpression" //next forbidden
                        Validation = NotNull
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
                        Type = Singleton "BasicExpression" //next allowed
                        Validation = NotNull
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
                        Type = Array "SingleAssignConstraint"
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
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "ModuleParameters"
                        Type = Array "Identifier"
                        Validation = None
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "ModuleElements"
                        Type = Array "ModuleElement"
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
                        Type = Singleton"Identifier"
                        Validation = NotNull
                        Comment = "."
                        CanBeNull = false
                    }
                    {
                        Name = "ModuleParameters"
                        Type = Array "BasicExpression" //next allowed
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
                        Type = Array "ModuleDeclaration"
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
                        Type = Singleton "Identifier"
                        Validation = None //no name necessary
                        Comment = "."
                        CanBeNull = true
                    }    
                    {
                        Name = "Expression"
                        Type = Singleton "SimpleExpression"
                        Validation = NotNull
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
                        Type = Singleton "ComplexIdentifier"
                        Validation = NotNull
                        Comment = "."
                        CanBeNull = false
                    }                    
                ]
            }
        ]
    }
    {
        // Chapter 2.4 Specifications p 35-42
        Name = "SafetySharp.Modelchecking.NuXmv.Specifications"
        Classes =
        [
            {  
                Name = "Specification"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }

            // Chapter 2.4.1 CTL Specifications p 35-36
            {   
                Name = "CtlSpecification"
                Base = "Specification"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "CtlExpression"
                        Type = Singleton "CtlExpression"
                        Validation = NotNull
                        Comment = "."
                        CanBeNull = false
                    }                      
                ]
            }

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
                        Type = Singleton "SimpleExpression"
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
                        Type = Singleton "CtlExpression"
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "NuXmvCtlBinaryOperator"
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = Singleton "CtlExpression"
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
                        Type = Singleton "CtlExpression"
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "NuXmvCtlUnaryOperator"
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                        CanBeNull = false
                    }
                ]
            }
            // Chapter 2.4.2 Invariant Specifications p 36
            //TODO
            // Chapter 2.4.3 LTL Specifications p 36-38
            {   
                Name = "LtlSpecification"
                Base = "Specification"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "LtlExpression"
                        Type = Singleton "LtlExpression"
                        Validation = NotNull
                        Comment = "."
                        CanBeNull = false
                    }                      
                ]
            }
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
                        Type = Singleton "SimpleExpression"
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
                        Type = Singleton "LtlExpression"
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "NuXmvLtlBinaryOperator"
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = Singleton "LtlExpression"
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
                        Type = Singleton "LtlExpression"
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "NuXmvLtlUnaryOperator"
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

