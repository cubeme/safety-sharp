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

[<EntryPoint>]
let main argv = 
    printfn " %s" Environment.NewLine
     
    printfn "SafetySharp Code Generator"
    printfn "Copyright (c) 2014 Institute for Software & Systems Engineering"
     
    printfn " %s" Environment.NewLine
    printfn "This is free software. You may redistribute copies of it under the terms of"
    printfn "the MIT license (see http://opensource.org/licenses/MIT)."
    printfn " %s" Environment.NewLine

    TestGenerator.Generate "../../Source/Tests/Generator/Test.Generated.cs"
    MetamodelGenerator.Generate "../../Source/SafetySharp/Metamodel/Metamodel.Generated.cs"
    FormulaeGenerator.Generate "../../Source/SafetySharp/Formulae/Formulae.Generated.cs"
    PromelaGenerator.Generate "../../Source/SafetySharp/Modelchecking/Promela/Promela.Generated.cs"
    NuXmvGenerator.Generate "../../Source/SafetySharp/Modelchecking/NuXmv/NuXmv.Generated.cs"

    printfn " %s" Environment.NewLine
    0