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

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading

#load "Generator.fsx"
open Generator

let outputFile = "SafetySharp/Metamodel/Metamodel.Generated.cs"
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
                        CollectionType = Generator.Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The name of the identifier."
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
                        Name = "Name"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the declared type."
                    }
                    {
                        Name = "Namespace"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The namespace the type is declared in."
                    }
                    {
                        Name = "Members"
                        Type = "MemberDeclaration"
                        CollectionType = Array
                        Validation = None
                        Comment = "The declared members of the type."
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
                        Name = "UpdateStatement"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The statement representing the Update method of the component."
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
                Name = "StateVariableDeclaration"
                Base = "MemberDeclaration"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The name of the state variable."
                    }
                    {
                        Name = "Type"
                        Type = "TypeReference"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The type of the state variable."
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
                    }
                    {
                        Name = "Statement"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The statement of the clause that can only be executed if the guard holds."
                    }
                ]
            }
            {   
                Name = "GuardedCommandExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Clauses"
                        Type = "GuardedCommandClause"
                        CollectionType = Array
                        Validation = None
                        Comment = "The clauses of the guarded command, one of which is chose nondeterministically during execution if multiple guards hold."
                    }
                ]
            }
            {   
                Name = "AssignmentExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the left-hand side of the assignment operator."
                    }
                    {
                        Name = "Right"
                        Type = "Expression"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The expression on the right-hand side of the assignment operator."
                    }
                ]
            }
            {   
                Name = "StateVariableExpression"
                Base = "Expression"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Variable"
                        Type = "StateVariableDeclaration"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The slot of the state variable."
                    }
                ]
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
                        Comment = "The expression that should be treated as a statement."
                    }
                ]
            }
            {   
                Name = "BlockStatement"
                Base = "Statement"
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

generateCode {
    Elements = elements
    OutputFile = outputFile
    BaseClass = "MetamodelElement"
    VisitorName = "MetamodelVisitor"
    RewriterName = "MetamodelRewriter"
    VisitorNamespace = "SafetySharp.Metamodel"
} 