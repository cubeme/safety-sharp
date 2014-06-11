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

namespace SafetySharp.Tests.Modeling.ComponentTests

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open Swensen.Unquote
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp.Syntax
open SafetySharp.CSharp
open SafetySharp.Metamodel
open SafetySharp.Modeling
open SafetySharp.Tests.CSharp

[<AutoOpen>]
module private ComponentTestsHelper =
    let createExpression<'T> (component' : Component) fieldName = 
        // This code depends on the F# compiler creating an internal field called 'fieldName@' for a 'val fieldName' expression
        let field = component'.GetType().GetField(fieldName + "@", BindingFlags.NonPublic ||| BindingFlags.Instance)
        if field = null then
            sprintf "Unable to find field '%s' in '%s'." fieldName (component'.GetType().FullName) |> invalidOp
        Expression.Lambda<Func<int>>(Expression.MakeMemberAccess(Expression.Constant(component'), field))

    type FieldComponent =
        inherit Component 
    
        val _field : int

        new () = { _field = 0 }
        new ([<ParamArray>] values : int array) as this = { _field = 0 } then
            this.SetInitialValues (createExpression<int> this "_field", values)

    type OneSubcomponent =
        inherit Component

        val _component : Component
        new component' = { _component = component' }

    type TwoSubcomponents =
        inherit Component

        val _component1 : Component
        val _component2 : Component

        new (component1, component2) = { _component1 = component1; _component2 = component2 }

[<TestFixture>]
module ``SetInitialValues method`` =
    [<Test>]
    let ``sets field value`` () =
        let component' = new FieldComponent(3)
        component'._field =? 3

        let component' = new FieldComponent(3, 182)
        (component'._field = 3 || component'._field = 182) =? true

    [<Test>]
    let ``throws when field expression is null`` () =
        let component' = new FieldComponent()
        raises<ArgumentNullException> <@ component'.SetInitialValues (null, 1, 2) @>

    [<Test>]
    let ``throws when initial values is null`` () =
        let component' = new FieldComponent()
        raises<ArgumentNullException> <@ component'.SetInitialValues (createExpression<int> component' "_field", null) @>

    [<Test>]
    let ``throws when initial values is empty`` () =
        let component' = new FieldComponent()
        raises<ArgumentException> <@ component'.SetInitialValues (createExpression<int> component' "_field") @>