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

namespace SafetySharp

open System
open System.Reflection
open SafetySharp

/// Provides helper functions for working with the reflection APIs.
module internal Reflection =

    /// The name of the resource that stores the embedded original S# assembly.
    [<Literal>]
    let EmbeddedAssembly = "OriginalAssembly"

    /// Gets all members of the given object recursively, going up the inheritance chain; unfortunately, the reflection APIs
    /// do not return private members of base classes, even with BindingFlags.FlattenHierarchy.
    let rec private getMembers selector (typeInfo : Type) (inheritanceRoot : Type) = seq {
        if typeInfo.BaseType <> null && typeInfo.BaseType <> inheritanceRoot then
            yield! getMembers selector typeInfo.BaseType inheritanceRoot
        
        yield! selector typeInfo (BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic ||| BindingFlags.DeclaredOnly)
    }

    /// Gets all fields declared by the given type or one of its base types up to the given root of the inheritance hierarchy.
    let getFields typeInfo inheritanceRoot = 
        getMembers (fun t b -> t.GetFields b) typeInfo inheritanceRoot

    /// Gets all properties declared by the given type or one of its base types up to the given root of the inheritance hierarchy.
    let getProperties typeInfo inheritanceRoot = 
        getMembers (fun t b -> t.GetProperties b) typeInfo inheritanceRoot

    /// Gets all methods declared by the given type or one of its base types up to the given root of the inheritance hierarchy.
    let getMethods typeInfo inheritanceRoot = 
        getMembers (fun t b -> t.GetMethods b) typeInfo inheritanceRoot

    /// Gets a value indicating whether the given member info is marked with an instance of the given attribute.
    let hasAttribute<'T> (info : MemberInfo) =
        info.GetCustomAttribute (typeof<'T>, false) <> null