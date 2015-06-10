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

namespace SafetySharp.Analysis

open System.Reflection
open SafetySharp
open SafetySharp.Modeling

/// <summary>
///     Provides access to a non-public field or property getter of a component.
/// </summary>
type internal IMemberAccess =
    /// <summary>
    ///     Gets the component instance that is accessed.
    /// </summary>
    abstract member Component : IComponent

    /// <summary>
    ///     Gets the name of the accessed field or property getter.
    /// </summary>
    abstract member MemberName : string

/// <summary>
///     Provides access to a non-public member of a component.
/// </summary>
/// <typeparam name="T">The type of the accessed member.</typeparam>
type MemberAccess<'T> internal (component', memberName) =
    let componentType = component'.GetType ()
    let bindingFlags = BindingFlags.Instance ||| BindingFlags.FlattenHierarchy ||| BindingFlags.Public ||| BindingFlags.NonPublic
    let fieldInfo = componentType.GetField (memberName, bindingFlags)
    let propertyInfo = componentType.GetProperty (memberName, bindingFlags)

    do if fieldInfo = null && propertyInfo = null then
        invalidOp "Component of type '%s' has no member with name '%s'." componentType.FullName memberName

    do if propertyInfo <> null && not propertyInfo.CanRead then
        invalidOp "Property '%s.%s' is write-only." componentType.FullName memberName

    let memberType = if fieldInfo <> null then fieldInfo.FieldType else propertyInfo.PropertyType
    do if memberType <> typeof<'T> then
        invalidOp "Expected '%s.%s' to be of type '%s', but actual type is '%s'." componentType.FullName memberName memberType.FullName typeof<'T>.FullName

    interface IMemberAccess with
        /// Gets the accessed component instance.
        override this.Component = component'

        /// Gets the name of the accessed member.
        override this.MemberName = memberName

    /// <summary>
    ///     Gets the current value of the accessed member.
    /// </summary>
    /// <param name="access">The member access the value should be retrieved for.</param>
    static member op_Implicit (access : MemberAccess<'T>) =
        access.Value

    /// Gets the current value of the accessed member.
    member internal this.Value = 
        if fieldInfo <> null then
            fieldInfo.GetValue component' :?> 'T
        else
            propertyInfo.GetValue component' :?> 'T

/// <summary>
///     Provides extension methods for analyzing <see cref="Component" /> instances.
/// </summary>
[<AutoOpen>]
module ComponentExtensions =
    type Component with
        /// <summary>
        ///     Allows access to a non-public member of the <paramref name="component" />.
        /// </summary>
        /// <typeparam name="T">The type of the accessed member.</typeparam>
        /// <param name="component">The component that should be accessed.</param>
        /// <param name="memberName">The name of the member that should be accessed.</param>
        /// <returns>Returns an <see cref="MemberAccess{T}" /> instance that can be used to access the non-public member.</returns>
        member this.Access<'T> (memberName : string) =
            nullOrWhitespaceArg memberName "memberName"
            MemberAccess<'T> (this, memberName)
