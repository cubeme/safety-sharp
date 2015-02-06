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
module ``Virtual dispatch`` =

    let private transform csharpCode = 
        let csharpCode = sprintf "%s class TestModel : Model { public TestModel() { SetRootComponents(new X()); } }" csharpCode
        let model = TestCompilation.CreateModel csharpCode
        model.FinalizeMetadata ()
        let root = CilToSsm.transformModel model |> SsmLowering.lowerVirtualCalls model
        root.Subs.[0]

    let private transformMethod csharpCode= 
        let ssm = transform csharpCode
        let loweredMethod = ssm.Methods |> Seq.filter (fun m -> m.Name.Contains("M")) |> Seq.exactlyOne
        match loweredMethod.Body with
        | SeqStm [ExprStm call; _] -> call
        | _ -> invalidOp "Unexpected method body."

    let private call name declaringType inheritanceLevel overloadIndex = 
        CallExpr (methodName name inheritanceLevel overloadIndex, declaringType, [], [], VoidType, [])

    let private memberCall field classType expr =
        MemberExpr (Field (field, ClassType classType), expr)

    [<Test>]
    let ``does not change non-virtual method`` () =
        transformMethod "class X : Component { void M() { N(); } void N() {} }" =? call "N" "X" 2 0

    [<Test>]
    let ``does not change virtual method at same level of hierarchy`` () =
        transformMethod "class X : Component { void M() { N(); } public virtual void N() {} }" =? call "N" "X" 2 0

    [<Test>]
    let ``does not change privately replaced virtual method`` () =
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { new void N() {} } class X : Component { Y z = new Z(); void M() { z.N(); }  }" =? 
            memberCall "Root0@0.z@0" "Y" (call "N" "Y" 2 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public override void N() {} } class Z : W { new void N() {} } class X : Component { Y z = new Z(); void M() { z.N(); }  }" =? 
            memberCall "Root0@0.z@0" "Y" (call "N" "W" 3 0)

    [<Test>]
    let ``does not change replaced virtual method`` () =
        transformMethod "class Y : Component { public virtual void N() {} } class X : Y { void M() { N(); } new void N() {} }" =? call "N" "X" 3 0
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { public new void N() {} } class X : Component { Z z = new Z(); void M() { z.N(); }  }" =? 
            memberCall "Root0@0.z@0" "Z" (call "N" "Z" 3 0)

    [<Test>]
    let ``changes virtual method to overridden one`` () =
        transformMethod "class Y : Component { void M() { N(); } public virtual void N() {} } class X : Y { public override void N() {} }" =? call "N" "X" 3 0
        transformMethod "class Y : Component { public virtual void N() {} } class X : Y { void M() { N(); } public override void N() {} }" =? call "N" "X" 3 0

        transformMethod "class Y : Component { void M() { N(); } public virtual void N() {} } class Z : Y {} class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { void M() { N(); } } class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y {} class X : Z { void M() { N(); } public override void N() {} }" =? call "N" "X" 4 0

        transformMethod "class Y : Component { void M() { N(); } public virtual void N() {} } class Z : Y { public override void N() {} } class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { void M() { N(); } public override void N() {} } class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { public override void N() {} } class X : Z { void M() { N(); } public override void N() {} }" =? call "N" "X" 4 0

    [<Test>]
    let ``changes abstract method to overridden one`` () =
        transformMethod "abstract class Y : Component { void M() { N(); } public abstract void N(); } class X : Y { public override void N() {} }" =? call "N" "X" 3 0
        transformMethod "abstract class Y : Component { public abstract void N(); } class X : Y { void M() { N(); } public override void N() {} }" =? call "N" "X" 3 0

        transformMethod "abstract class Y : Component { void M() { N(); } public abstract void N(); } abstract class Z : Y {} class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "abstract class Y : Component { public abstract void N(); } abstract class Z : Y { void M() { N(); } } class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "abstract class Y : Component { public abstract void N(); } abstract class Z : Y {} class X : Z { void M() { N(); } public override void N() {} }" =? call "N" "X" 4 0

        transformMethod "abstract class Y : Component { void M() { N(); } public abstract void N(); } class Z : Y { public override void N() {} } class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "abstract class Y : Component { public abstract void N(); } class Z : Y { void M() { N(); } public override void N() {} } class X : Z { public override void N() {} }" =? call "N" "X" 4 0
        transformMethod "abstract class Y : Component { public abstract void N(); } class Z : Y { public override void N() {} } class X : Z { void M() { N(); } public override void N() {} }" =? call "N" "X" 4 0

    [<Test>]
    let ``changes virtual method of subcomponent to overridden one`` () = 
        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { public override void N() {} } class X : Component { Y z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Y" (call "N" "X" 3 0)

        transformMethod "class Y : Component { public virtual void N() {} } class Z : Y { } class X : Component { Y z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Y" (call "N" "Z" 2 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public override void N() {} } class Z : W { } class X : Component { Y z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Y" (call "N" "Z" 3 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public override void N() {} } class Z : W { public override void N() {} } class X : Component { Y z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Y" (call "N" "Z" 4 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public override void N() {} } class Z : W { } class X : Component { Y z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Y" (call "N" "W" 3 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { } class Z : W { public override void N() {} } class X : Component { Y z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Y" (call "N" "Z" 4 0)

        transformMethod "class Y : Component { } class W : Y { } class Z : W { public virtual void N() {} } class X : Component { Z z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Z" (call "N" "Z" 4 0)

        transformMethod "class Y : Component { } class W : Y { public virtual void N() {} } class Z : W { } class X : Component { W z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "W" (call "N" "W" 3 0)

        transformMethod "class Y : Component { } class W : Y { public virtual void N() {} } class Z : W { public virtual void N() {} } class X : Component { Z z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Z" (call "N" "Z" 4 0)

    [<Test>]
    let ``changes virtual method replaced by another virtual method`` () =
        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public new virtual void N() {} } class Z : W { public virtual void N() {} } class X : Component { W z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "W" (call "N" "Z" 3 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public new virtual void N() {} } class Z : W { public virtual void N() {} } class X : Component { Z z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Z" (call "N" "Z" 4 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public new virtual void N() {} } class Z : W { } class X : Component { W z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "W" (call "N" "W" 3 0)

        transformMethod "class Y : Component { public virtual void N() {} } class W : Y { public new virtual void N() {} } class Z : W { } class X : Component { Z z = new Z(); public void M() { z.N(); }}" =?
            memberCall "Root0@0.z@0" "Z" (call "N" "W" 3 0)

    [<Test>]
    let ``changes interface method call`` () =
        transformMethod "interface I : IComponent { void N(); } class X : Component, I { public void N() {} void M() { N(); } }" =? call "N" "X" 2 0
        transformMethod "interface I : IComponent { void N(); } class X : Component, I { void I.N() {} void M() { ((I)this).N(); } }" =? call "N" "I" 2 0

    [<Test>]
    let ``calls correct interface method implemenation`` () =
        transformMethod "interface I : IComponent { void N(); } class Z : Component, I { public void N() {} } public class X : Component { I z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "I" (call "N" "I" 2 0)

        transformMethod "interface I : IComponent { void N(); } class Z : Component, I { void I.N() {} public void N() {} } public class X : Component { I z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "I" (call "N" "I" 2 0)

        transformMethod "interface I : IComponent { void N(); } class W : Component, I { public virtual void N() {} } class Z : W { public virtual void N() {} } public class X : Component { I z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "I" (call "N" "I" 3 0)

        transformMethod "interface I : IComponent { void N(); } abstract class W : Component, I { public abstract void N(); } class Z : W { public virtual void N() {} } public class X : Component { I z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "I" (call "N" "I" 3 0)

        transformMethod "interface I : IComponent { void N(); } class W : Component, I { public void N(); } class Z : W, I { void I.N() {} } public class X : Component { I z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "I" (call "N" "I" 3 0)

        transformMethod "interface I : IComponent { void N(); } interface J : I {} class W : Component, J { public void N() {} } class Z : W { } public class X : Component { J z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "J" (call "N" "J" 2 0)

        transformMethod "interface I : IComponent { void N(); } interface J : I {} class W : Component, J { public virtual void N() {} } class Z : W { public override void N() {} } public class X : Component { J z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "J" (call "N" "J" 3 0)

    [<Test>]
    let ``calls replaced interface method`` () =
        transformMethod "interface I : IComponent { void N(); } interface J : I { new void N(); } class W : Component, J { void I.N() {} void J.N() {} } class Z : W { } public class X : Component { J z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "J" (call "N" "J" 2 0)

        transformMethod "interface I : IComponent { void N(); } interface J : I { new void N(); } class W : Component, J { void I.N() {} void J.N() {} } class Z : W { } public class X : Component { I z = new Z(); void M() { z.N(); } }" =? 
            memberCall "Root0@0.z@0" "I" (call "N" "I" 2 0)

    [<Test>]
    let ``calls correct base method`` () =
        transformMethod "class Z : Component { public virtual void N() {} } class Y : Z {} class X : Y { public void M() { base.N(); } }" =? call "N" "Z" 2 0
        transformMethod "class Z : Component { public virtual void N() {} } class Y : Z { public override void N() {} } class X : Y { public void M() { base.N(); } }" =? call "N" "Y" 3 0
        transformMethod "class Z : Component { public virtual void N() {} } class Y : Z {} class X : Y { public override void N() {} public void M() { base.N(); } }" =? call "N" "Z" 2 0
        transformMethod "class Z : Component { public virtual void N() {} } class Y : Z { public override void N() {} } class X : Y { public override void N() {} public void M() { base.N(); } }" =? call "N" "Y" 3 0