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

namespace SafetySharp.Simulation
{
	using System;
	using System.Threading;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Simulates a S# model for visualization purposes or hardware-in-the-loop tests.
	/// </summary>
	public sealed class RealTimeSimulator
	{
		/// <summary>
		///     The model that is simulated.
		/// </summary>
		private readonly Model _model;

		/// <summary>
		///     The synchronization context that is used to marshal back to the main thread.
		/// </summary>
		private readonly SynchronizationContext _synchronizationContext = SynchronizationContext.Current;

		/// <summary>
		///     The current state of the simulation.
		/// </summary>
		private SimulationState _state;

		/// <summary>
		///     The time to wait between two simulation steps.
		/// </summary>
		private int _stepDelay;

		/// <summary>
		///     The timer that is used to schedule simulation updates.
		/// </summary>
		private Timer _timer;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="model">The model that should be simulated.</param>
		/// <param name="stepDelay">The step delay in milliseconds, i.e., time to wait between two steps in running mode.</param>
		public RealTimeSimulator(Model model, int stepDelay)
		{
			Requires.NotNull(model, () => model);
			Requires.That(SynchronizationContext.Current != null, "The simulator requires a valid synchronization context to be set.");

			model.FinalizeMetadata();

			_stepDelay = stepDelay;
			_model = model;

			_state = SimulationState.Stopped;
		}

		/// <summary>
		///     Gets the current state of the simulation.
		/// </summary>
		public SimulationState State
		{
			get { return _state; }
			set
			{
				if (_state == value)
					return;

				_state = value;
				if (SimulationStateChanged != null)
					SimulationStateChanged(this, EventArgs.Empty);

				if (_state != SimulationState.Running && _timer != null)
				{
					_timer.Dispose();
					_timer = null;
				}
				else if (_state == SimulationState.Running)
					_timer = new Timer(state1 => _synchronizationContext.Post(state2 => ExecuteStep(), null), null, 0, _stepDelay);
			}
		}

		/// <summary>
		///     Gets or sets the step delay in milliseconds, i.e., time to wait between two steps in running mode.
		/// </summary>
		public int StepDelay
		{
			get { return _stepDelay; }
			set
			{
				if (_stepDelay == value)
					return;

				_stepDelay = value;

				if (ModelStateChanged != null)
					ModelStateChanged(this, EventArgs.Empty);

				if (_timer != null)
					_timer.Change(_stepDelay, _stepDelay);
			}
		}

		/// <summary>
		///     Raised when the simulator's simulation state has been changed.
		/// </summary>
		public event EventHandler SimulationStateChanged;

		/// <summary>
		///     Raised when the simulated model state has been changed.
		/// </summary>
		public event EventHandler ModelStateChanged;

		/// <summary>
		///     Executes the next step of the simulation. This method can only be called when the simulation is paused or stopped.
		/// </summary>
		public void Step()
		{
			Requires.That(State != SimulationState.Running, "The simulation is already running.");

			State = SimulationState.Paused;
			ExecuteStep();
		}

		/// <summary>
		///     Runs the simulation in real-time mode. This method can only be called if the simulation is not already running.
		/// </summary>
		public void Run()
		{
			Requires.That(State != SimulationState.Running, "The simulation is already running.");
			Requires.That(SynchronizationContext.Current != null, "The simulation cannot be run without a valid SynchronizationContext.");

			State = SimulationState.Running;
		}

		/// <summary>
		///     Stops the simulation and resets it to its initial state. This method can only be called if the simulation is
		///     currently running or in paused mode.
		/// </summary>
		public void Stop()
		{
			Requires.That(State != SimulationState.Stopped, "The simulation is already stopped.");
			State = SimulationState.Stopped;

			_model.Reset();

			if (ModelStateChanged != null)
				ModelStateChanged(this, EventArgs.Empty);
		}

		/// <summary>
		///     Pauses the simulation. This method can only be called when the simulation is currently running.
		/// </summary>
		public void Pause()
		{
			Requires.That(State == SimulationState.Running, "Only running simulations can be stopped.");
			State = SimulationState.Paused;
		}

		/// <summary>
		///     Runs the simulation in non-real-time mode for the given <paramref name="timeSpan" />.
		/// </summary>
		/// <param name="timeSpan">The time span that should be simulated.</param>
		public void Simulate(TimeSpan timeSpan)
		{
			Requires.That(State == SimulationState.Stopped, "Expected the simulation to be stopped.");

			for (var i = 0; i < timeSpan.TotalSeconds; ++i)
				ExecuteStep();
		}

		/// <summary>
		///     Executes the next step of the simulation.
		/// </summary>
		private void ExecuteStep()
		{
			_model.ExecuteStep();

			if (ModelStateChanged != null)
				ModelStateChanged(this, EventArgs.Empty);
		}
	}
}