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

module MetamodelGenerator

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading
open Generator

let elements = [
    {
        Name = "SafetySharp.Metamodel"
        Classes =
        [
            {
                Name = "Identifier"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties =
                [
                    { 
                        Name = "Name"
                        Type = Singleton "string"
                        Validation = NotNullOrWhitespace
                        Comment = "The name of the identifier."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "MetamodelCompilation"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Resolver"
                        Type = Singleton "MetamodelResolver"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The resolver that can be used to resolve <cref see=\"IMetamodelReference\" />s within the model."
                    }
                    {
                        Name = "Components"
                        Type = Array "ComponentDeclaration"
                        Validation = None
                        CanBeNull = false
                        Comment = "The components declared in the model."
                    }  
                    {
                        Name = "Interfaces"
                        Type = Array "InterfaceDeclaration"
                        Validation = None
                        CanBeNull = false
                        Comment = "The component interfaces declared in the model."
                    }     
                ]
            }
            {
                Name = "MetamodelConfiguration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Partitions"
                        Type = Array "Partition"
                        Validation = None
                        CanBeNull = false
                        Comment = "The partitions declared in the model."
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Declarations"
        Classes = 
        [
            {   
                Name = "TypeDeclaration"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "The name of the declared type."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ComponentDeclaration"
                Base = "TypeDeclaration"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "UpdateMethod"
                        Type = Singleton "MethodDeclaration"
                        Validation = NotNull
                        Comment = "The Update method of the component."
                        CanBeNull = false
                    }
                    {
                        Name = "Methods"
                        Type = Array "MethodDeclaration"
                        Validation = None
                        Comment = "The methods declared by the component. The method overriding <see cref=\"SafetySharp.Modeling.Component.Update()\" /> is never contained in this set."
                        CanBeNull = false
                    }
                    {
                        Name = "Fields"
                        Type = Array "FieldDeclaration"
                        Validation = None
                        Comment = "The fields declared by the component."
                        CanBeNull = false
                    }
                    {
                        Name = "SubComponents"
                        Type = Array "SubComponentDeclaration"
                        Validation = None
                        Comment = "The sub components declared by the component."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "InterfaceDeclaration"
                Base = "TypeDeclaration"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "SubComponentDeclaration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The name of the sub component."
                    }
                    {
                        Name = "Type"
                        Type = Singleton "IMetamodelReference<TypeDeclaration>"
                        Validation = NotNull
                        Comment = "The type of the sub component."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "MethodDeclaration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The name of the method."
                    }
                    {
                        Name = "ReturnType"
                        Type = Singleton "TypeSymbol"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The return type of the method."
                    }
                    {
                        Name = "Parameters"
                        Type = Array "ParameterDeclaration"
                        Validation = None
                        CanBeNull = false
                        Comment = "The parameters of the method."
                    }
                    {
                        Name = "Body"
                        Type = Singleton "Statement"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The body of the method."
                    }
                ]
            }
            {   
                Name = "FieldDeclaration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "The name of the field."
                        CanBeNull = false
                    }
                    {
                        Name = "Type"
                        Type = Singleton "TypeSymbol"
                        Validation = NotNull
                        Comment = "The type of the field."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ParameterDeclaration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "The name of the parameter."
                        CanBeNull = false
                    }
                    {
                        Name = "Type"
                        Type = Singleton "TypeSymbol"
                        Validation = NotNull
                        Comment = "The type of the parameter."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Expressions"
        Classes = 
        [
            {   
                Name = "Expression"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "Literal"
                Base = "Expression"
                IsAbstract = true
                Properties = []
            }
            {
                Name = "BooleanLiteral"
                Base = "Literal"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = Singleton "bool"
                        Validation = None
                        Comment = "The Boolean value of the literal."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "IntegerLiteral"
                Base = "Literal"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = Singleton "int"
                        Validation = None
                        Comment = "The signed integer value of the literal."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "DecimalLiteral"
                Base = "Literal"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Value"
                        Type = Singleton "decimal"
                        Validation = None
                        Comment = "The decimal value of the literal."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "BinaryExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = Singleton "Expression"
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "BinaryOperator"
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = Singleton "Expression"
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the binary operator."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                Name = "UnaryExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Operand"
                        Type = Singleton "Expression"
                        Validation = NotNull
                        Comment = "The operand of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "UnaryOperator"
                        Validation = InRange
                        Comment = "The operator of the unary expression."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "FieldAccessExpression"
                Base = "Expression"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Field"
                        Type = Singleton "IMetamodelReference<FieldDeclaration>"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The reference to the <see cref=\"FieldDeclaration\" /> that is accessed by this expression."
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Statements"
        Classes = 
        [
            {   
                Name = "Statement"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "EmptyStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "BlockStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Statements"
                        Type = Array "Statement"
                        Validation = None
                        Comment = "The ordered list of statements the statement block consists of."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ReturnStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Expression"
                        Type = Singleton "Expression"
                        Validation = None
                        Comment = "The expression that should be evaluated and returned or <c>null</c> if the enclosing method returns <c>void</c>."
                        CanBeNull = true
                    }
                ]
            }
            {   
                Name = "GuardedCommandStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Clauses"
                        Type = Array "GuardedCommandClause"
                        Validation = None
                        Comment = "The clauses of the guarded command, one of which is chosen nondeterministically during execution if multiple guards hold."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "GuardedCommandClause"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Guard"
                        Type = Singleton "Expression"
                        Validation = NotNull
                        Comment = "The guard of the clause that determines whether the statement can be executed."
                        CanBeNull = false
                    }
                    {
                        Name = "Statement"
                        Type = Singleton "Statement"
                        Validation = NotNull
                        Comment = "The statement of the clause that can only be executed if the guard holds."
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
                        Type = Singleton "Expression"
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the assignment operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = Singleton "Expression"
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the assignment operator."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Types"
        Classes = 
        [
            {   
                Name = "TypeSymbol"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "VoidType"
                Base = "TypeSymbol"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "BooleanType"
                Base = "TypeSymbol"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "IntegerType"
                Base = "TypeSymbol"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "DecimalType"
                Base = "TypeSymbol"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "InterfaceType"
                Base = "TypeSymbol"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "InterfaceDeclaration"
                        Type = Singleton "IMetamodelReference<InterfaceDeclaration>"
                        Validation = NotNull
                        Comment = "The reference to the declaration of the interface."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Configurations"
        Classes = 
        [
            {
                Name = "Partition"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Component"
                        Type = Singleton "ComponentConfiguration"
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The root component configuration of the partition."
                    }
                ]
            }
            {   
                Name = "ComponentConfiguration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = Singleton "Identifier"
                        Validation = NotNull
                        Comment = "The name of the component configuration."
                        CanBeNull = false
                    }
                    {
                        Name = "Declaration"
                        Type = Singleton "ComponentDeclaration"
                        Validation = NotNull
                        Comment = "The declaration of the component configuration."
                        CanBeNull = false
                    }
                    {
                        Name = "Fields"
                        Type = Dictionary ("FieldDeclaration", "FieldConfiguration")
                        Validation = NotNull
                        Comment = "The field configurations for the fields declared by the component."
                        CanBeNull = false
                    }
                    {
                        Name = "SubComponents"
                        Type = Array "ComponentConfiguration"
                        Validation = None
                        Comment = "The sub component configurations of the component. The instances are specified in the same order as the corresponding sub component declarations of the component configuration's declaration."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "FieldConfiguration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "InitialValues"
                        Type = Array "object"
                        Validation = None
                        Comment = "The initial values of the field."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }
]

let Generate outputFile =
    generateCode {
        Elements = elements
        OutputFile = outputFile
        BaseClass = "MetamodelElement"
        VisitorName = "MetamodelVisitor"
        RewriterName = "MetamodelRewriter"
        Namespace = "SafetySharp.Metamodel"
        Visibility = Internal
    } 