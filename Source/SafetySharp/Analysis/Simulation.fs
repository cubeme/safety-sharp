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

open System
open System.Threading
open SafetySharp
open SafetySharp.Runtime.Modeling
open SafetySharp.Runtime.Simulation

/// Indicates the current state of a S# model simulation.
type SimulationState =
    /// Indicates that the simulation is currently not running.
    | Stopped = 0
    /// Indicates that the simulation is currently paused and can be resumed.
    | Paused = 1
    /// Indicates that the simulation is currently running.
    | Running = 2

/// Simulates a S# model for debugging or testing purposes.
type Simulator (model : Model) =
    do nullArg model "model"
    do model.FinalizeMetadata ()

    /// Runs the simulation for the given time span.
    member this.Simulate (timeSpan : TimeSpan) =
        for _ in 0 .. (int timeSpan.TotalSeconds) do
            this.ExecuteStep ()

    /// Executes the next step of the simulation.
    member private this.ExecuteStep () =
        // TODO: Respect explicit component scheduling
        let rec update (c : Component) =
            c.Subcomponents |> Seq.iter update
            //c.UpdateFaults ()
            c.Update ()

        update model.SynthesizedRoot

/// Simulates a S# model for visualization purposes or hardware-in-the-loop tests.
type RealTimeSimulator (model : Model, stepDelay : int) =
    do nullArg model "model"
    do invalidCall (SynchronizationContext.Current = null) "The simulator requires a valid synchronization context to be set."
    do model.FinalizeMetadata ()

    let mutable state = SimulationState.Stopped
    let mutable stepDelay = stepDelay
    let mutable timer : Timer = null
    let syncContext = SynchronizationContext.Current
    let stateChangedEvent = new Event<EventHandler, EventArgs> ()
    let modelChangedEvent = new Event<EventHandler, EventArgs> ()

    /// Gets the current state of the simulation.
    member this.State = state

    /// Raised when the simulator's simulation state has been changed.
    [<CLIEvent>]
    member this.SimulationStateChanged = stateChangedEvent.Publish

    /// Raised when the simulated model state has been changed.
    [<CLIEvent>]
    member this.ModelStateChanged = modelChangedEvent.Publish

    /// Gets or sets the step delay in milliseconds, i.e., time to wait between two steps in running mode.
    member this.StepDelay
        with get () = stepDelay
        and set value = 
            if stepDelay <> value then
                stepDelay <- value
                stateChangedEvent.Trigger (null, EventArgs.Empty)
                if timer <> null then timer.Change (stepDelay, stepDelay) |> ignore

    /// Executes the next step of the simulation. This method can only be called when the simulation is paused or stopped.
    member this.Step () =
        invalidCall (state = SimulationState.Running) "The simulation is already running."

        this.ChangeState SimulationState.Paused
        this.ExecuteStep ()

    /// Runs the simulation in real-time mode. This method can only be called if the simulation is not already running.
    member this.Run () =
        invalidCall (state = SimulationState.Running) "The simulation is already running."
        invalidCall (SynchronizationContext.Current = null) "The simulation cannot be run without a valid SynchronizationContext."

        this.ChangeState SimulationState.Running

    /// Stops the simulation and resets it to its initial state. This method can only be called if the simulation is 
    /// currently running or in paused mode.
    member this.Stop () =
        invalidCall (state = SimulationState.Stopped) "The simulation is already stopped."
        this.ChangeState SimulationState.Stopped

        let rec reset (c : Component) =
            c.Subcomponents |> Seq.iter reset
           // c.Reset ()

        reset model.SynthesizedRoot
        modelChangedEvent.Trigger (this, EventArgs.Empty)

    /// Pauses the simulation. This method can only be called when the simulation is currently running.
    member this.Pause () =
        invalidCall (state <> SimulationState.Running) "Only running simulations can be stopped."
        this.ChangeState SimulationState.Paused

    /// Runs the simulation in non-real-time mode for the given time span.
    member this.Simulate (timeSpan : TimeSpan) =
        invalidCall (state <> SimulationState.Stopped) "Expected the simulation to be stopped."

        for _ in 0 .. (int timeSpan.TotalSeconds) do
            this.ExecuteStep ()

    /// Executes the next step of the simulation.
    member private this.ExecuteStep () =
        // TODO: Respect explicit component scheduling
        let rec update (c : Component) =
            c.Subcomponents |> Seq.iter update
            //c.UpdateFaults ()
            c.Update ()

        update model.SynthesizedRoot
        modelChangedEvent.Trigger (this, EventArgs.Empty)  

    /// Changes the state of the simulator.
    member private this.ChangeState newState =
        state <- newState
        stateChangedEvent.Trigger (this, EventArgs.Empty)

        if state <> SimulationState.Running && timer <> null then 
            timer.Dispose ()
            timer <- null
        elif state = SimulationState.Running then
            timer <- new Timer ((fun _ -> syncContext.Post ((fun _ -> this.ExecuteStep ()), null)), null, 0, stepDelay)