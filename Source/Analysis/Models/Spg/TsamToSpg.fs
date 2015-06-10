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

namespace SafetySharp.Models


module internal TsamToSpg =
    open Tsam
    open Spg
    
    (*
    type StochasticTransition = {
        Label:string;
        FromState:State;
        ToStates:(int*Expr*State) list; // (ChoiceNumber*Probability*TargetStatement)
    }
    
    type DeterministicTransition = {
        Label:string;
        FromState:State;
        ToState:State;
        Guard:Expr option;
        Action:(Var*Expr) option;
    }

    type IndeterministicTransition = {
        Label:string;
        FromState:State;
        ToStates:State list;
    }

    type CollectedInformation = {
        InitialState : State;
        EndState : State;
        States : State list ref;
        StochasticTransitions : StochasticTransition list ref;
        IndeterministicTransitions : IndeterministicTransition list ref;
        DeterministicTransitions : DeterministicTransition list ref;
        //StateToStatementId : Map<State,StatementId> ref;
        UniqueStateIdGenerator : unit -> StateId;
    }
    *)
    
    let rec collectStatesAndTransitions (alreadyCollected:StochasticProgramGraph) (previousState:State,nextState:State) (stm:Stm) : StochasticProgramGraph =
        // Every case should connect previousState with nextState. They may introduce additional states in between.
        match stm with
            | Stm.Assert (sid,expr) ->
                // TODO: Assert has no real meaning in the control flow
                let newEntry =
                    {
                        DeterministicTransition.Label=sprintf "Assert%d" (sid.id);
                        DeterministicTransition.FromState=previousState;
                        DeterministicTransition.ToState=nextState;
                        DeterministicTransition.Guard=Some(expr);
                        DeterministicTransition.Action=None;
                    }
                { alreadyCollected with
                    DeterministicTransitions = alreadyCollected.DeterministicTransitions.Add newEntry
                }
            | Stm.Assume (sid,expr) ->
                let newEntry =
                    {
                        DeterministicTransition.Label=sprintf "Assume%d" (sid.id);
                        DeterministicTransition.FromState=previousState;
                        DeterministicTransition.ToState=nextState;
                        DeterministicTransition.Guard=Some(expr);
                        DeterministicTransition.Action=None;
                    }
                { alreadyCollected with
                    DeterministicTransitions = alreadyCollected.DeterministicTransitions.Add newEntry
                }
            | Stm.Block (blockSid,stmts) ->
                let nextStateAfterBlock = nextState
                let previousStateBeforeBlock = previousState

                if stmts.IsEmpty then
                    // connect previousStateBeforeBlock directly with nextStateAfterBlock
                    let newEntry =
                        {
                            DeterministicTransition.Label=sprintf "Block%dConnect" (blockSid.id);
                            DeterministicTransition.FromState=previousStateBeforeBlock;
                            DeterministicTransition.ToState=nextStateAfterBlock;
                            DeterministicTransition.Guard=None;
                            DeterministicTransition.Action=None;
                        }
                    { alreadyCollected with
                        DeterministicTransitions = alreadyCollected.DeterministicTransitions.Add newEntry
                    }
                else
                    let noOfBetweenStates = (stmts.Length - 1)
                    let statePositionToState,newStates : Map<int,State>*(Set<State>) =
                        // Example: Assume 3 Statements
                        //     * Position 0 |-> previousStateBeforeBlock
                        //     * Position 1 |-> created betweenState 1
                        //     * Position 2 |-> created betweenState 2
                        //     * Position 3 = Position (stmts.Length) |-> nextStateAfterBlock
                        //    In the transition from
                        //     * Position 0 to 1 Stm1 is executed
                        //     * Position 1 to 2 Stm2 is executed
                        //     * Position 2 to 3 Stm3 is executed) 
                        let newStates : Set<State> ref = ref Set.empty<State>
                        let createBetweenState (number:int) : State =                            
                            let newBetweenState =
                                {
                                    State.StateId = alreadyCollected.UniqueStateIdGenerator ();
                                    State.Label = sprintf "Block%dBetween%d" (blockSid.id) (number);
                                }
                            do newStates := newStates.Value.Add newBetweenState
                            newBetweenState
                        let positionsBetweenStates = seq {1..noOfBetweenStates} |> Seq.toList |> List.map (fun number -> (number,createBetweenState number)) |> Map.ofList                    
                        let positionsAll =
                            positionsBetweenStates.Add(0,previousStateBeforeBlock)
                                                  .Add(stmts.Length,nextStateAfterBlock)
                        (positionsAll,newStates.Value)
                    let fromMap : Map<Stm,State> =
                        let fromStatePositions = seq {0..stmts.Length - 1} |> Seq.toList
                        List.zip fromStatePositions stmts |> List.map (fun (previousStateNo,stm) -> (stm,statePositionToState.Item previousStateNo) ) |> Map.ofList
                    let toMap : Map<Stm,State> =
                        let toStatePositions = seq {1..stmts.Length} |> Seq.toList
                        List.zip toStatePositions stmts |> List.map (fun (nextStateNo,stm) -> (stm,statePositionToState.Item nextStateNo) ) |> Map.ofList
                    let alreadyCollectedWithNewStates=
                        { alreadyCollected with
                            States = Set.union alreadyCollected.States newStates;
                        }
                    let foldSubStatement (spg:StochasticProgramGraph) (stm:Stm) : StochasticProgramGraph =
                        let previousState = fromMap.Item stm
                        let nextState = toMap.Item stm
                        collectStatesAndTransitions (spg) (previousState,nextState) stm
                    let alreadyCollectedWithSubstatements = stmts |> List.fold foldSubStatement alreadyCollectedWithNewStates
                    alreadyCollectedWithSubstatements
            | Stm.Choice (choiceSid,choices:Stm list) ->
                let traverseSubStatementAndCreateSubProgramGraph (stm:Stm) : (StochasticProgramGraph*State) =
                    let newState =
                        {
                            State.StateId = alreadyCollected.UniqueStateIdGenerator ();
                            State.Label = sprintf "Choice%dNo%d" (choiceSid.id) (stm.GetStatementId.id);
                        }
                    let alreadyCollectedForSubStatements =
                        let statesInSubGraph = Set.empty<State>.Add(newState).Add(nextState)
                        StochasticProgramGraph.initial (alreadyCollected.Variables) statesInSubGraph newState (alreadyCollected.UniqueStateIdGenerator)
                    let subProgramGraph = collectStatesAndTransitions alreadyCollectedForSubStatements (newState,nextState) stm
                    (subProgramGraph,newState)
                let (subProgramGraphs,connectionStatesToProgramGraphs) =
                    choices |> List.map traverseSubStatementAndCreateSubProgramGraph |> List.unzip
                let stochasticProgramGraphWithSubProgramGraphs =
                    alreadyCollected.unionWithMany subProgramGraphs

                let connectionsToSubProgramGraphs =
                    let newEntryForConnection (connectionState:State) =
                        {
                            DeterministicTransition.Label=sprintf "Choice%dNo" (stm.GetStatementId.id);
                            DeterministicTransition.FromState=previousState;
                            DeterministicTransition.Guard=None;
                            DeterministicTransition.Action=None;
                            DeterministicTransition.ToState=connectionState;
                        }
                    connectionStatesToProgramGraphs |> List.map newEntryForConnection |> Set.ofList
                let stochasticProgramGraphWithSubProgramGraphsAndConnections =
                    { stochasticProgramGraphWithSubProgramGraphs with
                        DeterministicTransitions = Set.union stochasticProgramGraphWithSubProgramGraphs.DeterministicTransitions connectionsToSubProgramGraphs
                    }
                stochasticProgramGraphWithSubProgramGraphsAndConnections
            | Stm.Stochastic (choiceSid,stochasticChoices) ->
                let traverseSubStatementAndCreateSubProgramGraph (number:int,(probability:Expr,stm:Stm)) : (StochasticProgramGraph*StochasticOption) =
                    let newState =
                        {
                            State.StateId = alreadyCollected.UniqueStateIdGenerator ();
                            State.Label = sprintf "Stochastic%dNo%d" (choiceSid.id) (stm.GetStatementId.id);
                        }
                    let alreadyCollectedForSubStatements =
                        let statesInSubGraph = Set.empty<State>.Add(newState).Add(nextState)
                        StochasticProgramGraph.initial (alreadyCollected.Variables) statesInSubGraph newState (alreadyCollected.UniqueStateIdGenerator)
                    let subProgramGraph = collectStatesAndTransitions alreadyCollectedForSubStatements (newState,nextState) stm                    
                    let stochasticOption =
                        {
                            StochasticOption.Number = number;
                            StochasticOption.Probability = probability;
                            StochasticOption.Action = None;
                            StochasticOption.ToState = newState;
                        }
                    (subProgramGraph,stochasticOption)
                let (subProgramGraphs,stochasticOptions) =
                    let numbers = seq {1..(stochasticChoices.Length)} |> Seq.toList
                    let numberedChoices = List.zip numbers stochasticChoices
                    numberedChoices |> List.map traverseSubStatementAndCreateSubProgramGraph |> List.unzip
                let stochasticProgramGraphWithSubProgramGraphs =
                    alreadyCollected.unionWithMany subProgramGraphs

                let stochasticTransition =
                    {
                        StochasticTransition.Label=sprintf "Stochastic%dNo" (stm.GetStatementId.id);
                        StochasticTransition.FromState=previousState;
                        StochasticTransition.Guard=None;
                        StochasticTransition.Options=stochasticOptions;
                    }
                let stochasticProgramGraphWithSubProgramGraphsAndConnections =
                    { stochasticProgramGraphWithSubProgramGraphs with
                        StochasticTransitions = stochasticProgramGraphWithSubProgramGraphs.StochasticTransitions.Add stochasticTransition
                    }
                stochasticProgramGraphWithSubProgramGraphsAndConnections

            | Stm.Write (sid,var,expr) ->
                let newEntry =
                    {
                        DeterministicTransition.Label=sprintf "Write%d" (sid.id);
                        DeterministicTransition.FromState=previousState;
                        DeterministicTransition.ToState=nextState;
                        DeterministicTransition.Guard=None;
                        DeterministicTransition.Action=Some(var,expr);
                    }
                { alreadyCollected with
                    DeterministicTransitions = alreadyCollected.DeterministicTransitions.Add newEntry
                }
    
    
    let transformToStochasticProgramGraph (pgm:Pgm) : StochasticProgramGraph =
        let uniqueStateIdGenerator =
            let stmIdCounter : int ref = ref 0 // this stays in the closure
            let generator () : StateId =
                do stmIdCounter := stmIdCounter.Value + 1
                StateId(stmIdCounter.Value)
            generator
        let initialState =
            {
                State.Label = "initialState";
                State.StateId = uniqueStateIdGenerator ();
            }
        let endState =
            {
                State.Label = "endState";
                State.StateId = uniqueStateIdGenerator ();
            }
        let initialCollectedInformation =
            let states = Set.empty.Add(initialState).Add(endState)
            let vardecls =
                let globals = pgm.Globals
                let locals = pgm.Locals |> List.map (fun l -> {GlobalVarDecl.Var=l.Var;GlobalVarDecl.Type=l.Type;GlobalVarDecl.Init=[l.Type.getDefaultValue]})
                globals@locals
            StochasticProgramGraph.initial vardecls states initialState uniqueStateIdGenerator

        let transformed = collectStatesAndTransitions initialCollectedInformation (initialState,endState) (pgm.Body)
        transformed


    open SafetySharp.Workflow
    open SafetySharp.Models.SpgTracer

    let transformToStochasticProgramGraphWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,StochasticProgramGraphTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let transformed =
            {
                StochasticProgramGraphTracer.ProgramGraph = transformToStochasticProgramGraph (state.Pgm);
                StochasticProgramGraphTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                StochasticProgramGraphTracer.ForwardTracer = state.ForwardTracer;
            }
        do! updateState transformed
    }