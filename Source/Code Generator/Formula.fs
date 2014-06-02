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

module FormulaGenerator

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading
open Generator

let elements = [
    {
        Name = "SafetySharp.Formulas"
        Classes =
        [
            {
                Name = "StateFormula"
                Base = "Formula"
                IsAbstract = false
                Properties =
                [
                    { 
                        Name = "Expression"
                        Type = Singleton "SafetySharp.Metamodel.Expressions.Expression"
                        Validation = NotNull
                        Comment = "The metamodel expression that represents the state formula."
                        CanBeNull = false
                    }
                    { 
                        Name = "AssociatedComponent"
                        Type = Singleton "SafetySharp.Metamodel.Configurations.ComponentConfiguration"
                        Validation = None
                        Comment = "The associated component is the scope in which the expression is evaluated."
                        CanBeNull = true
                    }
                ]
            }
            {
                Name = "UntransformedStateFormula"
                Base = "Formula"
                IsAbstract = false
                Properties =
                [
                    { 
                        Name = "Expression"
                        Type = Singleton "string"
                        Validation = NotNull
                        Comment = "The untransformed C# expression as a string that represents the state formula."
                        CanBeNull = false
                    }
                    { 
                        Name = "Values"
                        Type = Array "object"
                        Validation = None
                        Comment = "The non-literal values referenced by the C# expression."
                        CanBeNull = false
                    }
                ]
            }
            {   
                Name = "BinaryFormula"
                Base = "Formula"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Left"
                        Type = Singleton "Formula"
                        Validation = NotNull
                        Comment = "The formula on the left-hand side of the binary operator."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "BinaryTemporalOperator"
                        Validation = InRange
                        Comment = "The operator of the binary formula."
                        CanBeNull = false
                    }
                    {
                        Name = "PathQuantifier"
                        Type = Singleton "PathQuantifier"
                        Validation = InRange
                        Comment = "The path quantifier of the binary formula."
                        CanBeNull = false
                    }
                    {
                        Name = "Right"
                        Type = Singleton "Formula"
                        Validation = NotNull
                        Comment = "The formula on the right-hand side of the binary operator."
                        CanBeNull = false
                    }
                ]
            }            
            {   
                Name = "UnaryFormula"
                Base = "Formula"
                IsAbstract = false
                Properties = 
                [
                    {
                        Name = "Operand"
                        Type = Singleton "Formula"
                        Validation = NotNull
                        Comment = "The operand of the unary formula."
                        CanBeNull = false
                    }
                    {
                        Name = "Operator"
                        Type = Singleton "UnaryTemporalOperator"
                        Validation = InRange
                        Comment = "The operator of the unary formula."
                        CanBeNull = false
                    }
                    {
                        Name = "PathQuantifier"
                        Type = Singleton "PathQuantifier"
                        Validation = InRange
                        Comment = "The path quantifier of the unary formula."
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
        BaseClass = "Formula"
        VisitorName = "FormulaVisitor"
        RewriterName = "FormulaRewriter"
        Namespace = "SafetySharp.Formulas"
        Visibility = Internal
    } 