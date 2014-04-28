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

let outputFile = "SafetySharp/Modelchecking/Promela/Promela.Generated.cs"
let elements = [
    {
        Name = "SafetySharp.Modelchecking.Promela"
        Classes =
        [
            {
                Name = "Identifier"
                Base = "PromelaElement"
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
]

generateCode {
    Elements = elements
    OutputFile = outputFile
    BaseClass = "PromelaElement"
    VisitorName = "PromelaVisitor"
    RewriterName = "PromelaRewriter"
    VisitorNamespace = "SafetySharp.Modelchecking.Promela"
} 