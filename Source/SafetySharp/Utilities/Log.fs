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

namespace SafetySharp.Utilities

open System
open System.Diagnostics
open Microsoft.FSharp.Core

/// Identifies the type of information provided by a <see cref="LogEntry" />.
type internal LogType =
    | Fatal
    | Error
    | Warning
    | Info
    | Debug

/// Represents a log entry, describing fatal errors, non-fatal errors, or warnings as well as providing debugging
/// information and other informational messages.
type internal LogEntry = {
    Type : LogType
    Message : string
    Time : DateTime
}

/// Provides globally accessible functions to log fatal errors, non-fatal errors, warnings, informational messages, and
/// debug-time only informational messages. The <see cref="Logged" /> event is raised whenever a <see cref="LogEntry" /> has
/// been generated.
[<AbstractClass; Sealed>]
type internal Log () =
    [<DefaultValue>] static val mutable private logged : Event<LogEntry>

    static do
        Log.logged <- Event<LogEntry> ()
        Log.Logged.Add Log.PrintToDebugOutput

    /// Raises the <see cref="LogEntry" /> event with the given log entry type and message.
    static member private RaiseEvent logType message =
        Log.logged.Trigger { Type = logType; Message = message; Time = DateTime.Now }

    /// Writes all generated log entries to the debug output.
    static member private PrintToDebugOutput logEntry =
        let logType = 
            match logEntry.Type with
            | Debug     -> "Debug  "
            | Info      -> "Info   "
            | Warning   -> "Warning"
            | Error     -> "Error  "
            | Fatal     -> "Fatal  "

        Debug.WriteLine ("[{0}] {1}", logType, logEntry.Message)

    /// Raised when a <see cref="LogEntry" /> has been generated. If the <see cref="LogEntry" />'s type is
    /// <see cref="LogType.Fatal" />, the program terminates after all event handlers have been executed.
    static member Logged : IEvent<LogEntry> = Log.logged.Publish

    /// Logs a fatal application error and terminates the application after all event handlers of the <see cref="Logged" />
    /// event have been executed.
    static member Die message =  Printf.ksprintf (fun message -> Log.RaiseEvent Fatal message; Environment.Exit -1) message

    /// Logs an application error.
    static member Error message = Printf.ksprintf (Log.RaiseEvent Error) message

    /// Logs an application warning.
    static member Warn message = Printf.ksprintf (Log.RaiseEvent Warning) message

    /// Logs an informational message.
    static member Info message = Printf.ksprintf (Log.RaiseEvent Info) message

    /// In debug builds, logs debugging information. We cannot apply the Condition attribute to the actual Debug method
    /// defined below, as that would cause compiler errors in Release builds.
    [<Conditional("DEBUG")>]
    static member private Debug message = Log.RaiseEvent Debug message

    /// In debug builds, logs debugging information.
    static member Debug message = Printf.ksprintf (Log.Debug) message
