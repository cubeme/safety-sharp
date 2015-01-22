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

namespace Utilities

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open SafetySharp.CSharpCompiler.Utilities

module Log =
    [<Test>]
    let ``Info method`` () =
        let invoked = ref false
        let logged = Action<LogEntry> (fun logEntry ->
                logEntry.LogType =? LogType.Info
                logEntry.Message =? "Info 1 2"
                invoked := true)

        try
            Log.add_Logged logged
            Log.Info ("Info {0} {1}", 1, 2)
            !invoked =? true

        finally
            Log.remove_Logged logged

    [<Test>]
    let ``Warn method`` () =
        let invoked = ref false
        let logged = Action<LogEntry> (fun logEntry ->
                logEntry.LogType =? LogType.Warning
                logEntry.Message =? "Warning 1 2"
                invoked := true)

        try
            Log.add_Logged logged
            Log.Warn ("Warning {0} {1}", 1, 2)
            !invoked =? true

        finally
            Log.remove_Logged logged

    [<Test>]
    let ``Error method`` () =
        let invoked = ref false
        let logged = Action<LogEntry> (fun logEntry ->
                logEntry.LogType =? LogType.Error
                logEntry.Message =? "Error 1 2"
                invoked := true)

        try
            Log.add_Logged logged
            Log.Error ("Error {0} {1}", 1, 2)
            !invoked =? true

        finally
            Log.remove_Logged logged

    [<Test>]
    let ``Die method`` () =
        let invoked = ref false
        let invokedDie = ref false

        let onDie = Action (fun () -> invokedDie := true)

        let logged = Action<LogEntry> (fun logEntry ->
                logEntry.LogType =? LogType.Fatal
                logEntry.Message =? "Die 1 2"
                invoked := true)

        try
            Log.add_Logged logged
            Log.add_OnDie onDie

            Log.Die ("Die {0} {1}", 1, 2)
            !invoked =? true
            !invokedDie =? true

        finally
            Log.remove_Logged logged
            Log.remove_OnDie onDie
