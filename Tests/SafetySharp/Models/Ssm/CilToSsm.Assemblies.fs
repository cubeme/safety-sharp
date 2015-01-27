// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace Ssm

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm
open SafetySharp.Tests

[<TestFixture>]
module ``CilToSsm Multiple Assemblies`` =
    let private transform supportingCode mainCode instantiations =
        let supportCompilation = TestCompilation supportingCode
        let supportAssembly = supportCompilation.Compile ()
        let compilation = TestCompilation (sprintf "class T : Model { public T() { SetRootComponents(%s); } } %s" instantiations mainCode, supportAssembly)
        let assembly = compilation.Compile ()
        let modelType = assembly.GetType "T"
        let model = Activator.CreateInstance modelType :?> Model
        model.FinalizeMetadata ()
        CilToSsm.transformModel model

    [<Test>]
    let ``subcomponent of type in other assembly`` () =
        transform "public class X : Component { public void M() {} }" "class Y : Component { X x = new X(); void N() { x.M(); }}" "new Y()" =?
            [
                {
                    Name = "Root0"
                    Fields = []
                    Subs = 
                        [
                            {
                                Name = "Root0.x@0"
                                Fields = []
                                Subs = []
                                Methods = 
                                [
                                    {
                                        Name = CilToSsm.makeUniqueMethodName "M" 2 0
                                        Return = VoidType
                                        Params = []
                                        Locals = []
                                        Body = RetStm None
                                        Kind = ProvPort
                                    } 
                                ]
                            } 
                        ]
                    Methods = 
                        [
                            {
                                Name = CilToSsm.makeUniqueMethodName "N" 2 0
                                Return = VoidType
                                Params = []
                                Locals = []
                                Body = SeqStm [CallStm ({ Name = CilToSsm.makeUniqueMethodName "M" 2 0; Type = "X" }, [], [], VoidType, [], Some (VarExpr (Field (CilToSsm.makeUniqueFieldName "x" 2, ClassType "X")))); RetStm None]
                                Kind = ProvPort
                            } 
                        ]
                }
            ]

    [<Test>]
    let ``inherit from type in other assembly`` () =
        transform "public class X : Component { protected bool b; public void M() {} }" "class Y : X { void N() { M(); b = true; }}" "new Y()" =?
            [
                {
                    Name = "Root0"
                    Fields = [{ Var = Field (CilToSsm.makeUniqueFieldName "b" 2, BoolType); Init = [BoolVal false] }]
                    Subs = []
                    Methods =
                    [
                        {
                            Name = CilToSsm.makeUniqueMethodName "M" 2 0
                            Return = VoidType
                            Params = []
                            Locals = []
                            Body = RetStm None
                            Kind = ProvPort
                        } 
                        {
                            Name = CilToSsm.makeUniqueMethodName "N" 3 0
                            Return = VoidType
                            Params = []
                            Locals = []
                            Body = SeqStm 
                                [
                                    CallStm ({ Name = CilToSsm.makeUniqueMethodName "M" 2 0; Type = "X" }, [], [], VoidType, [], Some (VarExpr (This (ClassType "Y"))))
                                    AsgnStm (Field (CilToSsm.makeUniqueFieldName "b" 2, BoolType), BoolExpr true)
                                    RetStm None
                                ]
                            Kind = ProvPort
                        } 
                    ]
                }
            ]

