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
open System.Collections.Generic
open System.Dynamic
open System.Globalization
open System.Linq
open System.Linq.Expressions
open System.Reflection
open System.Runtime.InteropServices
open SafetySharp
open Mono.Cecil

/// Provides helper functions for working with the reflection APIs.
module internal Reflection =
    /// Gets all members of the given object recursively, going up the inheritance chain; unfortunately, the reflection APIs
    /// do not return private members of base classes, even with BindingFlags.FlattenHierarchy.
    let rec private getMembers selector (t : Type) = seq {
        if t.BaseType <> null then
            yield! getMembers selector t.BaseType
        
        yield! selector t (BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)
    }

    /// Gets all fields declared by the given type.
    let getFields t = 
        getMembers (fun t b -> t.GetFields b) t

    /// Gets all properties declared by the given type.
    let getProperties t = 
        getMembers (fun t b -> t.GetProperties b) t

    /// Gets all methods declared by the given type.
    let getMethods t = 
        getMembers (fun t b -> t.GetMethods b) t

    /// Gets a value indicating whether the given member info is marked with an instance of the given attribute.
    let hasAttribute<'T> (info : MemberInfo) =
        info.GetCustomAttribute (typeof<'T>, false) <> null