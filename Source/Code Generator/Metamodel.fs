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
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The name of the identifier."
                        CanBeNull = false
                    }
                ]
            }
            {
                Name = "Model"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties =
                [
                    {
                        Name = "Components"
                        Type = "ComponentDeclaration"
                        CollectionType = Array
                        Validation = None
                        CanBeNull = false
                        Comment = "The components declared in the compilation unit."
                    }       
                    {
                        Name = "Resolver"
                        Type = "MetamodelResolver"
                        CollectionType = Singleton
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The resolver that can be used to resolve <cref see=\"MetamodelReference\" />s within the model."
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
                Name = "ComponentDeclaration"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the declared type."
                        CanBeNull = false
                    }
                    {
                        Name = "UpdateMethod"
                        Type = "MethodDeclaration"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The Update method of the component."
                        CanBeNull = false
                    }
                    {
                        Name = "Methods"
                        Type = "MethodDeclaration"
                        CollectionType = Array
                        Validation = None
                        Comment = "The methods declared by the component. The method overriding <see cref=\"SafetySharp.Modeling.Component.Update()\" /> is never contained in this set."
                        CanBeNull = false
                    }
                    {
                        Name = "Fields"
                        Type = "FieldDeclaration"
                        CollectionType = Array
                        Validation = None
                        Comment = "The fields declared by the component."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "MemberDeclaration"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "MethodDeclaration"
                Base = "MemberDeclaration"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The name of the method."
                    }
                    {
                        Name = "Body"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        CanBeNull = false
                        Comment = "The body of the method."
                    }
                ]
            }
            {   
                Name = "FieldDeclaration"
                Base = "MemberDeclaration"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Identifier"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the field."
                        CanBeNull = false
                    }
                    {
                        Name = "Type"
                        Type = "TypeReference"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The type of the field."
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
                        Type = "bool"
                        CollectionType = Singleton
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
                        Type = "int"
                        CollectionType = Singleton
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
                        Type = "decimal"
                        CollectionType = Singleton
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
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "BinaryOperator"
                        CollectionType = Singleton
                        Validation = InRange
                        Comment = "The operator of the binary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = "Expression"
                        CollectionType = Singleton
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
                        Name = "Expression"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression of the unary expression."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = "UnaryOperator"
                        CollectionType = Singleton
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
                        Type = "MetamodelReference<FieldDeclaration>"
                        CollectionType = Singleton
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
                        Type = "Statement"
                        CollectionType = Array
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
                        Type = "Expression"
                        CollectionType = Singleton
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
                Base = "MetamodelElement"
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
                Name = "AssignmentStatement"
                Base = "Statement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the assignment operator."
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
        ]
    }
    {
        Name = "SafetySharp.Metamodel.TypeReferences"
        Classes = 
        [
            {   
                Name = "TypeReference"
                Base = "MetamodelElement"
                IsAbstract = true
                Properties = []
            }
            {   
                Name = "VoidTypeReference"
                Base = "TypeReference"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "BooleanTypeReference"
                Base = "TypeReference"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "IntegerTypeReference"
                Base = "TypeReference"
                IsAbstract = false
                Properties = []
            }
            {   
                Name = "InterfaceTypeReference"
                Base = "TypeReference"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Slot"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The slot of the interface declaration in the model's type information table."
                        CanBeNull = false
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Instances"
        Classes = 
        [
            {   
                Name = "ComponentInstance"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "InitialValues"
                        Type = "Expression"
                        CollectionType = Array
                        Validation = None
                        Comment = "The initial values."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "Binding"
                Base = "MetamodelElement"
                IsAbstract = false
                Properties = 
                [
                ]
            }
        ]
    }
]

let generateMetamodel outputFile =
    generateCode {
        Elements = elements
        OutputFile = outputFile
        BaseClass = "MetamodelElement"
        VisitorName = "MetamodelVisitor"
        RewriterName = "MetamodelRewriter"
        VisitorNamespace = "SafetySharp.Metamodel"
        Public = true
    } 