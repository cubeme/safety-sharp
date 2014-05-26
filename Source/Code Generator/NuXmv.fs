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
            (*{   
                Name = "Proctype"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "IsActive"
                        Type = "bool"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "If true then Proctype gets automatically executed at startup."
                        CanBeNull = false
                    }
                    {
                        Name = "Name"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the Proctype."
                        CanBeNull = false
                    }
                    {
                        Name = "Code"
                        Type = "Statement"
                        CollectionType = Array
                        Validation = None
                        Comment = "A list of statements with the code of the Proctype."
                        CanBeNull = false
                    }
                ]
            }*)
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
            //TODO: Move into own enum
            {
                Name = "SignSpecifier"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "UnsignedSpecifier"
                Base = "SignSpecifier"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "SignedSpecifier"
                Base = "SignSpecifier"
                IsAbstract = false
                Properties = []
            }
            {
                //Radix of numeral system
                Name = "Radix"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "BinaryRadix"
                Base = "Radix"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "OctalRadix"
                Base = "Radix"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "DecimalRadix"
                Base = "Radix"
                IsAbstract = false
                Properties = []
            }
            {
                Name = "HexadecimalRadix"
                Base = "Radix"
                IsAbstract = false
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
                Name = "NuXmvType"
                Base = "PromelaElement"
                IsAbstract = true
                Properties = []
            }
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
                        Type = "Literal"
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
                        Type = "int32"
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
                        Type = "int32"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Lower bound of the array."
                        CanBeNull = false
                    }
                    {
                        Name = "Upper"
                        Type = "int32"
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
        // Chapter 2.2 Expressions p 10-22
        Name = "SafetySharp.Modelchecking.NuXmv.Expressions"
        Classes = 
        [
            {   
                Name = "Expression"
                Base = "NuXmvElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "BasicExpression"
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
                        Type = "BigInteger"
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
                        Type = "BitArray"
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
                        Type = "Radix"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "Radix of Numeral System (binary, octal, decimal or hexadecimal)."
                        CanBeNull = false
                    }
                    {
                        Name = "SignSpecifier"
                        Type = "SignSpecifier"
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
                        Type = "BigInteger"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The value the range starts with (inclusive)."
                        CanBeNull = false
                    }
                    {
                        Name = "To"
                        Type = "BigInteger"
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
    // Chapter 2.3 Definition of the FSM p 22-35
    // Chapter 2.3.1 Variable Declarations p 23-26
    // TODO: Declarations may include numbers for their definition,
    //       Should these integers be written down directly as a number
    //       or by expressions, which can be evaluated statically to a number?
    // Chapter 2.3.2 DEFINE Declarations p 26
    // Chapter 2.3.3 Array Define Declarations p 26-27
    // Chapter 2.3.4 CONSTANTS Declarations p 27
    // Chapter 2.3.5 INIT Constraint p 27
    // Chapter 2.3.6 INVAR Constraint p 27
    // Chapter 2.3.7 TRANS Constraint p 28
    // Chapter 2.3.8 ASSIGN Constraint p 28-29
    // Chapter 2.3.9 FAIRNESS Constraints p 30
    // Chapter 2.3.10 MODULE Declarations p 30-31
    // Chapter 2.3.11 MODULE Instantiations p 31
    // Chapter 2.3.12 References to Module Components (Variables and Defines) p 32-33
    // Chapter 2.3.13 A Program and the main Module p 33
    // Chapter 2.3.14 Namespaces and Constraints on Declarations p 33
    // Chapter 2.3.15 Context p 34
    // Chapter 2.3.16 ISA Declarations p 34
    // Chapter 2.3.17 PRED and MIRROR Declarations p 34-35


    // Chapter 2.4.1 CTL Specifications p 35-36
    // Chapter 2.4.2 Invariant Specifications p 36
    // Chapter 2.4.3 LTL Specifications p 36-38
    // Chapter 2.4.4 Real Time CTL Specifications and Computations p 38-39
    // Chapter 2.4.5 PSL Specifications p 39-42
    // Chapter 2.5 Variable Order Input p 42-44
    
    (*
    {
        Name = "SafetySharp.Modelchecking.NuXmv.Statements"
        Classes = 
        [
            {   
                Name = "Statement"
                Base = "PromelaElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "BlockStatement"
                Base = "Statement"
                IsAbstract = true
                Properties = 
                [
                    {
                        Name = "Statements"
                        Type = "Statement"
                        CollectionType = Array
                        Validation = None
                        Comment = "A list of statements."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "SimpleBlockStatement"
                Base = "BlockStatement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "AtomicBlockStatement"
                Base = "BlockStatement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "DStepBlockStatement"
                Base = "BlockStatement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "ReturnStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression that should be evaluated and returned."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ExpressionStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression that should be evaluated."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "SkipStatement" //Convenience and generated code gets prettier. In Promela it is equivalent to a ExpressionStatement with the Boolean Literal True
                Base = "Statement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "GuardedCommandRepetitionStatement"  //do :: od
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Clauses"
                        Type = "GuardedCommandClause"
                        CollectionType = Array
                        Validation = None
                        Comment = "The clauses of the guarded command, one of which is chosen nondeterministically during execution if multiple guards hold."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "GuardedCommandSelectionStatement" //if :: fi
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Clauses"
                        Type = "GuardedCommandClause"
                        CollectionType = Array
                        Validation = None
                        Comment = "The clauses of the guarded command, one of which is chosen nondeterministically during execution if multiple guards hold."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "GuardedCommandClause"
                Base = "PromelaElement"
                IsAbstract = true
                Properties = []
            }          
            {   
                Name = "GuardedCommandExpressionClause"
                Base = "GuardedCommandClause"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Guard"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The guard of the clause that determines whether the statement can be executed."
                        CanBeNull = false
                    }
                    {
                        Name = "Statement"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The statement of the clause that can only be executed if the guard holds."
                        CanBeNull = false
                    }
                ]
            }          
            {   
                Name = "GuardedCommandElseClause"
                Base = "GuardedCommandClause"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Statement"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The statement of the clause that can only be executed if no other clause holds."
                        CanBeNull = false
                    }
                ]
            }          
            {   
                Name = "AssignmentStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "VariableReferenceExpression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The reference to the variable on the left-hand side of the assignment operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the assignment operator."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "DeclarationStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Type"
                        Type = "PromelaTypeName"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The type of the declared variable."
                        CanBeNull = false
                    }
                    {
                        Name = "Identifier"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the declared variable."
                        CanBeNull = false
                    }
                    {
                        Name = "ArraySize"
                        Type = "Int32"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The size of the array, if declared variable is an array. Otherwise 0."
                        CanBeNull = false
                    }
                    {
                        Name = "InitialValue"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "An expression, which determines the initial value of the declared variable."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }*)
]

let generateNuXmv outputFile =
    generateCode {
        Elements = elements
        OutputFile = outputFile
        BaseClass = "NuXmvElement"
        VisitorName = "NuXmvVisitor"
        RewriterName = "NuXmvRewriter"
        Namespace = "SafetySharp.Modelchecking.NuXmv"
        Public = false
    }

