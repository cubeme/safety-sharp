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

module TestGenerator

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading
open Generator

let elements = [
    {
        Name = "Tests.Generator"
        Classes = 
        [
            {
                Name = "TestBase"
                Base = "TestElement"
                IsAbstract = true
                Properties = 
                [
                    {
                        Name = "NullObject"
                        Type = "object"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The object that can be null."
                        CanBeNull = true
                    }
                    {
                        Name = "NotNullObject"
                        Type = "object"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The not-null object."
                        CanBeNull = false
                    }
                    {
                        Name = "NotEmpty"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The non-empty string."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "InheritedValidationTestElement"
                Base = "TestBase"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Value"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The integer value."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ValidationTestElement"
                Base = "TestElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "NullObject"
                        Type = "object"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The object that can be null."
                        CanBeNull = true
                    }
                    {
                        Name = "NotNullObject"
                        Type = "object"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The not-null object."
                        CanBeNull = false
                    }
                    {
                        Name = "NotEmpty"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The non-empty string."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "SimpleTestElement"
                Base = "TestElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Value"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The value."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ArrayTestElement"
                Base = "TestElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Array"
                        Type = "SimpleTestElement"
                        CollectionType = Array
                        Validation = None
                        Comment = "The test array."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "ListTestElement"
                Base = "TestElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "List"
                        Type = "SimpleTestElement"
                        CollectionType = List
                        Validation = NotNull
                        Comment = "The list that cannot be null."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "NullListTestElement"
                Base = "TestElement"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "List"
                        Type = "SimpleTestElement"
                        CollectionType = List
                        Validation = None
                        Comment = "The list that cannot be null."
                        CanBeNull = true
                    }
                ]
            }
        ]
    }
]

let generateTest outputFile =
    generateCode {
        Elements = elements
        OutputFile = outputFile
        BaseClass = "TestElement"
        VisitorName = "TestVisitor"
        RewriterName = "TestRewriter"
        Namespace = "Tests.Generator"
        Public = false
    } 