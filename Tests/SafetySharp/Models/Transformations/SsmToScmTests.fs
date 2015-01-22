// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineeringgineering
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

namespace Transformations

open System
open NUnit.Framework
open SafetySharp.Models
open SafetySharp.Models.Transformations

[<TestFixture>]
module ``SsmToScm Transformation`` =

    [<Test>]
    let ``simple component without subcomponents`` () =
        SsmToScm.transform {
            Name = "X"
            Subs = []
            Fields = [Ssm.Field ("f", Ssm.IntType); Ssm.Field ("b", Ssm.BoolType)]
            Methods = 
            [
                {
                    Name = "M"
                    Params = []
                    Body = 
                        Ssm.SeqStm [
                            Ssm.RetStm None
                        ]
                    Return = Ssm.VoidType
                    Locals = [Ssm.Local ("x", Ssm.IntType)]
                    Kind = Ssm.ProvPort
                }
            ]
        } =? {
            Comp = Scm.Comp "X"
            Subs = []
            Fields = [{ Field = Scm.Field "f"; Type = Scm.IntType; Init = []};{ Field = Scm.Field "b"; Type = Scm.BoolType; Init = []}]
            ProvPorts = 
                [
                    {
                        FaultExpr = None
                        ProvPort = Scm.ProvPort "M"
                        Params = []
                        Behavior = 
                        {
                            Locals = [{ Var = Scm.Var "x"; Type = Scm.IntType }]
                            Body = Scm.Block []
                        }
                    }
                ]
            ReqPorts = []
            Steps = []
            Faults = []
            Bindings = []
        }