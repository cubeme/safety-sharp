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

namespace SafetySharp.Modeling

open SafetySharp
open System
open System.Reflection

/// When applied to a method or property of a <see cref="Component" /> class or a <see cref="IComponent" /> interface, 
/// marks the method or property as a provided port.
[<AttributeUsage(AttributeTargets.Method ||| AttributeTargets.Property, AllowMultiple = false, Inherited = false)>]
[<Sealed; AllowNullLiteral>]
type ProvidedAttribute () =
    inherit Attribute ()

/// When applied to a method or property of a <see cref="Component" /> class or a <see cref="IComponent" /> interface, 
/// marks the method or property as a required port.
[<AttributeUsage(AttributeTargets.Method ||| AttributeTargets.Property, AllowMultiple = false, Inherited = false)>]
[<Sealed; AllowNullLiteral>]
type RequiredAttribute () =
    inherit Attribute ()

/// For S#-internal use only.
[<AttributeUsage(AttributeTargets.Method ||| AttributeTargets.Property, AllowMultiple = false, Inherited = false)>]
[<Sealed; AllowNullLiteral>]
type BackingFieldAttribute (backingField : string) =
    inherit Attribute ()

    /// Gets the name of the backing field.
    member internal this.BackingField = backingField

    /// Gets the reflected field for the given type.
    member internal this.GetFieldInfo (t : Type) =
        let field = t.GetField(this.BackingField, BindingFlags.DeclaredOnly ||| BindingFlags.Instance ||| BindingFlags.NonPublic)
        if field = null then invalidOp "Unable to find backing field '%s.%s'." (t.FullName) this.BackingField
        field