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

/// Defines a set of test helper functions and operators that are shared between all test projects.
/// The test helpers are defined in the global namespace within an auto-open module so that all
/// testing code can conveniently use those helpers.
[<AutoOpen>]
module TestHelpers

open System
open System.Collections
open System.Collections.Generic
open System.Linq
open System.Linq.Expressions
open System.IO
open System.Text
open System.Reflection
open System.Runtime.CompilerServices
open SafetySharp
open SafetySharp.Models
open SafetySharp.Modeling
open SafetySharp.Reflection
open Microsoft.FSharp.Reflection
open NUnit.Framework

module private ObjectDumper =
 
    /// Dumps the given object for debugging purposes.
    let dump (object' : obj) =
        
        let duplicationCheck = HashSet<obj> ({ new IEqualityComparer<obj> with
            member this.Equals (symbol1, symbol2) = 
                obj.ReferenceEquals (symbol1, symbol2)
            member this.GetHashCode symbol =
                RuntimeHelpers.GetHashCode symbol
        })

        let maxLevel = 5
        let currentLevel = ref 0
        let writer = StructuredWriter ()
        let asEnumerable (object' : obj) = 
            (object' :?> IEnumerable).Cast<obj> ()

        let rec dumpEnumerable (elements : obj seq) front back =
            writer.AppendBlock (fun () -> writer.AppendRepeated elements dump (fun () -> writer.Append ", ")) front back

        and dumpMap (elements : obj seq) =
            let elements = Array.ofSeq elements
            if elements.Length = 0 then
                writer.Append "[]"
            else
                let keyProperty = elements.[0].GetType().GetProperty "Key"
                let valueProperty = elements.[0].GetType().GetProperty "Value"

                writer.Append "Map ["
                writer.IncreaseIndent ()
                writer.NewLine ()
                for element in elements do
                    writer.AppendBlockStatement (fun () ->
                        writer.AppendBlock (fun () -> dump (keyProperty.GetValue element)) "Key =" ""
                        writer.AppendBlock (fun () -> dump (valueProperty.GetValue element)) "Value =" ""
                    ) 
                    writer.NewLine ()
                writer.DecreaseIndent ()
                writer.Append "]"

        and dumpObject (object' : obj) =
            let dumpProperties typeName (properties : PropertyInfo array) =
                writer.Append "%s" typeName
                if properties.Length > 0 then
                    writer.AppendBlock (fun () ->
                        writer.AppendRepeated properties (fun property -> 
                            writer.Append "%s = " property.Name 
                            dump (property.GetValue object')
                        ) (fun () -> writer.AppendLine ",")
                    ) "{" "}"

            let objectType = object'.GetType ()
            if FSharpType.IsUnion (objectType, true) then
                let (info, values) = FSharpValue.GetUnionFields (object', objectType, true)
                writer.Append "%s" info.Name
                if values.Length = 1 then
                    writer.Append " "
                    dump values.[0]
                elif values.Length > 1 then
                    writer.AppendBlock (fun () -> writer.AppendRepeated values dump (fun () -> writer.AppendLine ", ")) "(" ")"
            elif FSharpType.IsRecord (objectType, true) then
                dumpProperties objectType.Name <| FSharpType.GetRecordFields (objectType, true)
            elif FSharpType.IsTuple objectType then
                writer.Append "("
                writer.AppendRepeated (FSharpValue.GetTupleFields object') dump (fun () -> writer.Append ", ")
                writer.Append ")"
            else
                incr currentLevel 
                if !currentLevel >= maxLevel then
                    writer.Append "..."
                else
                    let bindingFlags = BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic
                    let properties = objectType.GetProperties bindingFlags |> Seq.where (fun property -> property.CanRead) |> Array.ofSeq
                    dumpProperties objectType.Name properties
                decr currentLevel

        and dump (object' : obj) : unit =
            try
                if duplicationCheck.Add object' = false && not (object' :? string) && not (FSharpType.IsUnion (object'.GetType (), true)) then
                    writer.Append "#object has already been dumped elsewhere#"
                elif object' = null then
                    writer.Append "null"
                else
                    let objectType = object'.GetType ()
                    if objectType.IsArray then
                        dumpEnumerable (asEnumerable object') "[|" "|]"
                    elif objectType.FullName.StartsWith "Microsoft.FSharp.Collections.FSharpList" then
                        dumpEnumerable (asEnumerable object') "[" "]"
                    elif objectType.FullName.StartsWith "Microsoft.FSharp.Collections.FSharpMap" then
                        dumpMap <| asEnumerable object'
                    elif object' :? string then
                        writer.Append "%A" object'
                    elif objectType.FullName.StartsWith "Microsoft.FSharp.Core.FSharpOption" then
                        dump (object'.GetType().GetProperty("Value").GetValue object')
                    elif object' :? IEnumerable then
                        dumpEnumerable (asEnumerable object') "seq {" "}"
                    elif objectType.IsEnum then
                        writer.Append "%s.%A" (object'.GetType().Name) object'
                    elif objectType.IsPrimitive then
                        writer.Append "%A" object'
                    else
                        dumpObject object'
            with e -> writer.Append "#exception#"

        dump object'
        writer.ToString ()

/// Checks whether the given function raises an exception of the given type.
let raisesWith<'T when 'T :> Exception> func =
    let mutable thrownException : Exception option = None
    try 
        func ()
    with 
    | :? 'T as e -> 
        thrownException <- Some <| upcast e
    | e ->
        thrownException <- Some e

    match thrownException with
    | None ->
        Assert.Fail ("Expected an exception of type '{0}', but no exception was thrown.", typeof<'T>.FullName)
        Unchecked.defaultof<'T>
    | Some (:? 'T as e) ->
        e
    | Some e ->
        let message = "Expected an exception of type '{0}', but an exception of type '{1}' was thrown instead.\n\nActual:\n{2}"
        Assert.Fail (message, typeof<'T>.FullName, e.GetType().FullName, ObjectDumper.dump e)
        Unchecked.defaultof<'T>

/// Checks whether the given function raises an exception of the given type.
let raises<'T when 'T :> Exception> func =
    raisesWith<'T> func |> ignore

/// Checks whether the given function raises an <see cref="InvalidOperationException"/>.
let raisesInvalidOpException func =
    raises<InvalidOperationException> func |> ignore

/// Checks whether the given function raises an <see cref="ArgumentNullException"/> for the argument with the given name.
let raisesArgumentNullException argumentName func =
    let e = raisesWith<ArgumentNullException> func
    Assert.AreEqual (argumentName, e.ParamName, "Expected exception to be thrown for argument '{0}', but was thrown for '{1}'.", argumentName, e.ParamName)

/// Checks whether the given function raises an <see cref="ArgumentException"/> for the argument with the given name.
let raisesArgumentException argumentName func =
    let e = raisesWith<ArgumentException> func
    Assert.AreEqual (argumentName, e.ParamName, "Expected exception to be thrown for argument '{0}', but was thrown for '{1}'.", argumentName, e.ParamName)

/// Catches the given exception type and rethrows the inner exception.
let unwrap<'T when 'T :> Exception> func =
    let e = raisesWith<'T> func
    raise e.InnerException |> ignore

/// Checks whether the given function raises no exception.
let nothrow func =
    try
        func ()
    with
    | e -> 
        let message = "Expected no exception to be thrown, but an exception of type '{0}' was raised:\n{1}"
        Assert.Fail (message, e.GetType().FullName, ObjectDumper.dump e)

/// Asserts that the two values are equal.
let (=?) actual expected =
    let result = actual = expected
    if not result then
        let actual = ObjectDumper.dump actual
        let expected = ObjectDumper.dump expected
        Assert.Fail ("Objects are not equal, even though they are expected to be equal.\n\nExpected:\n{0}\n\nActual:\n{1}", expected, actual)

/// Asserts that the two values are not equal.
let (<>?) actual expected =
    let result = actual <> expected
    if not result then
        Assert.Fail ("Objects are equal, even though they are expected to be different.\n\n{0}", ObjectDumper.dump expected)

/// Normalizes all new lines to '\n' only.
let normalizeNewLines (str : string) =
    str.Replace ("\r", String.Empty)

let methodName = Renaming.makeUniqueMethodName
let fieldName = Renaming.makeUniqueFieldName


let internal addLogEventHandlerForXUnit<'state> (output:Xunit.Abstractions.ITestOutputHelper) : SafetySharp.Workflow.EndogenousWorkflowFunction<'state> = 
    let behavior (wfState:SafetySharp.Workflow.WorkflowState<'state>) =
        do wfState.LogEvent.Publish.Add (
            fun text -> output.WriteLine text
        )
        (),wfState
    SafetySharp.Workflow.WorkflowFunction(behavior)
