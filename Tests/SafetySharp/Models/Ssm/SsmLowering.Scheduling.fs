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

namespace Models.Ssm.Lowering

open System
open System.Linq
open NUnit.Framework
open Mono.Cecil
open SafetySharp.Modeling
open SafetySharp.Models
open SafetySharp.Models.Ssm

[<TestFixture>]
module ``Scheduling`` =

    let private transform csharpCode roots = 
        let csharpCode = sprintf "%s class TestModel : Model { public TestModel() { AddRootComponents(%s); } }" csharpCode roots
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        CilToSsm.transformModel model |> SsmLowering.lowerScheduling

    let private checkSchedule selector subs c =
        let c = selector c
        let step = c.Methods |> Seq.find (fun m -> m.Kind = Step)
        match step.Body with
        | SeqStm s ->
            List.length s =? (List.length subs + 1)
            Seq.zip (s |> Seq.take (List.length subs)) subs
            |> Seq.iter (fun (actual, expected) ->
                match actual with
                | ExprStm (MemberExpr (t, m)) -> 
                    Ssm.getVarName t =? expected
                    match m with
                    | CallExpr ("Update", _, _, _, _, _, _) -> ()
                    | _ -> failwith "Expected Update method call."
                | _ -> failwith "Expected a method call."
            )
        | _ when subs = [] -> ()
        | _ -> failwith "Step method does not invoke subcomponent step methods."

    [<Test>]
    let ``synthesized root schedules subcomponent`` () =
        transform "class X : Component {}" "new X()" 
        |> checkSchedule id ["X0@0"]

    [<Test>]
    let ``synthesized root schedules two subcomponents in correct order`` () =
        transform "class X : Component {} class Y : Component {}" "new X(), new Y()" 
        |> checkSchedule id ["X0@0"; "Y1@1"]

    [<Test>]
    let ``synthesized root schedules three subcomponents in correct order`` () =
        transform "class X : Component {} class Y : Component {} class Z : Component {}" "new X(), new Y(), new Z()" 
        |> checkSchedule id ["X0@0"; "Y1@1"; "Z2@2"]

    [<Test>]
    let ``component without subcomponent`` () =
        transform "class X : Component {}" "new X()" |> checkSchedule (fun c -> c.Subs.[0]) []

    [<Test>]
    let ``component schedules subcomponent`` () =
        transform "class X : Component { Y y = new Y(); } class Y : Component {}" "new X()" 
        |> checkSchedule (fun c -> c.Subs.[0]) ["y@0"]

    [<Test>]
    let ``component schedules two subcomponents in correct order`` () =
        transform "class X : Component { Y y1 = new Y(); Y y2 = new Y(); } class Y : Component {}" "new X()" 
        |> checkSchedule (fun c -> c.Subs.[0]) ["y1@0"; "y2@1"]

    [<Test>]
    let ``component schedules four subcomponents in correct order`` () =
        transform "class X : Component { Y y1 = new Y(); Z a = new Z(); Z z = new Z(); Y y2 = new Y(); } class Y : Component {} class Z : Component {}" "new X()" 
        |> checkSchedule (fun c -> c.Subs.[0]) ["y1@0"; "a@1"; "z@2"; "y2@3"]

    [<Test; Ignore>]
    let ``inherited component schedules four subcomponents in correct order`` () =
        transform "class W : Component { Y y1 = new Y(); Z a = new Z(); } class X : W { Z z = new Z(); Y y2 = new Y(); } class Y : Component {} class Z : Component {}" "new X()" 
        |> checkSchedule (fun c -> c.Subs.[0]) ["y1@0"; "a@1"; "z@2"; "y2@3"]
