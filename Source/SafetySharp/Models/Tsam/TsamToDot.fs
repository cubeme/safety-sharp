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


module internal TsamToDot =
    open Tsam
    
    let rec exportExpr (expr:Expr) : string =
        let result = TsamToString.exportExpr expr SamToStringHelpers.AstToStringState.initial
        result.ToString ()
    
    type StateId = StateId of int
    
    type State = {
        Label : string;
        StateId : StateId;
    }
    
    type StochasticTransition = {
        Label:string;
        FromState:State;
        ToStates:(int*Expr*State) list; // (ChoiceNumber*Probability*TargetStatement)
    }

    type IndeterministicTransition = {
        Label:string;
        FromState:State;
        ToStates:State list;
    }

    type DeterministicTransition = {
        Label:string;
        FromState:State;
        ToState:State;
        Guard:Expr option;
        Action:(Var*Expr) option;
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

    let rec collectStatesAndTransitions (alreadyCollected:CollectedInformation) (previousState:State,nextState:State) (stm:Stm) : unit =
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
                do alreadyCollected.DeterministicTransitions := newEntry::alreadyCollected.DeterministicTransitions.Value
                ()
            | Stm.Assume (sid,expr) ->
                let newEntry =
                    {
                        DeterministicTransition.Label=sprintf "Assume%d" (sid.id);
                        DeterministicTransition.FromState=previousState;
                        DeterministicTransition.ToState=nextState;
                        DeterministicTransition.Guard=Some(expr);
                        DeterministicTransition.Action=None;
                    }
                do alreadyCollected.DeterministicTransitions := newEntry::alreadyCollected.DeterministicTransitions.Value
                ()
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
                    do alreadyCollected.DeterministicTransitions := newEntry::alreadyCollected.DeterministicTransitions.Value
                    ()
                else
                    let noOfBetweenStates = (stmts.Length - 1) 
                    let statePositionToState : Map<int,State> =
                        // Example: Assume 3 Statements
                        //     * Position 0 |-> previousStateBeforeBlock
                        //     * Position 1 |-> created betweenState 1
                        //     * Position 2 |-> created betweenState 2
                        //     * Position 3 = Position (stmts.Length) |-> nextStateAfterBlock
                        //    In the transition from
                        //     * Position 0 to 1 Stm1 is executed
                        //     * Position 1 to 2 Stm2 is executed
                        //     * Position 2 to 3 Stm3 is executed
                        let createBetweenState (number:int) : State =                            
                            let newBetweenState =
                                {
                                    State.StateId = alreadyCollected.UniqueStateIdGenerator ();
                                    State.Label = sprintf "Block%dBetween%d" (blockSid.id) (number);
                                }
                            do alreadyCollected.States := newBetweenState::alreadyCollected.States.Value
                            newBetweenState
                        let positionsBetweenStates = seq {1..noOfBetweenStates} |> Seq.toList |> List.map (fun number -> (number,createBetweenState number)) |> Map.ofList                    
                        let positionsAll =
                            positionsBetweenStates.Add(0,previousStateBeforeBlock)
                                                  .Add(stmts.Length,nextStateAfterBlock)
                        positionsAll
                    let fromMap : Map<Stm,State> =
                        let fromStatePositions = seq {0..stmts.Length - 1} |> Seq.toList
                        List.zip fromStatePositions stmts |> List.map (fun (previousStateNo,stm) -> (stm,statePositionToState.Item previousStateNo) ) |> Map.ofList
                    let toMap : Map<Stm,State> =
                        let toStatePositions = seq {1..stmts.Length} |> Seq.toList
                        List.zip toStatePositions stmts |> List.map (fun (nextStateNo,stm) -> (stm,statePositionToState.Item nextStateNo) ) |> Map.ofList
                    let traverseSubStatement (stm:Stm) =
                        let previousState = fromMap.Item stm
                        let nextState = toMap.Item stm
                        do collectStatesAndTransitions (alreadyCollected) (previousState,nextState) stm
                        ()
                    do stmts |> List.iter traverseSubStatement
                    ()
            | Stm.Choice (choiceSid,choices:Stm list) ->
                let createSubstateAndTraverseSubStatement (stm:Stm) : State =
                    let newState =
                        {
                            State.StateId = alreadyCollected.UniqueStateIdGenerator ();
                            State.Label = sprintf "Choice%dNo%d" (choiceSid.id) (stm.GetStatementId.id);
                        }                        
                    do alreadyCollected.States := newState::alreadyCollected.States.Value
                    do collectStatesAndTransitions alreadyCollected (newState,nextState) stm
                    newState
                let choiceStates = choices |> List.map createSubstateAndTraverseSubStatement
                let newEntry =
                    {
                        IndeterministicTransition.Label=sprintf "Choice%dNo" (stm.GetStatementId.id);
                        IndeterministicTransition.FromState=previousState;
                        IndeterministicTransition.ToStates=choiceStates;
                    }
                do alreadyCollected.IndeterministicTransitions := newEntry::alreadyCollected.IndeterministicTransitions.Value
                ()
            | Stm.Stochastic (choiceSid,stochasticChoices) ->
                let createSubstateAndTraverseSubStatement (number:int,(expr:Expr,stm:Stm)) : int*Expr*State =
                    let newState =
                        {
                            State.StateId = alreadyCollected.UniqueStateIdGenerator ();
                            State.Label = sprintf "Stochastic%dNo%d" (choiceSid.id) (stm.GetStatementId.id);
                        }
                    do alreadyCollected.States := newState::alreadyCollected.States.Value
                    do collectStatesAndTransitions alreadyCollected (newState,nextState) stm
                    (number,expr,newState)
                let stochasticChoiceStates =
                    let numbers = seq {1..(stochasticChoices.Length)} |> Seq.toList
                    List.zip numbers stochasticChoices |> List.map createSubstateAndTraverseSubStatement
                let newEntry =
                    {
                        StochasticTransition.Label=sprintf "Stochastic%dNo" (stm.GetStatementId.id);
                        StochasticTransition.FromState=previousState;
                        StochasticTransition.ToStates=stochasticChoiceStates;
                    }
                do alreadyCollected.StochasticTransitions := newEntry::alreadyCollected.StochasticTransitions.Value
                ()
            | Stm.Write (sid,var,expr) ->
                let newEntry =
                    {
                        DeterministicTransition.Label=sprintf "Write%d" (sid.id);
                        DeterministicTransition.FromState=previousState;
                        DeterministicTransition.ToState=nextState;
                        DeterministicTransition.Guard=None;
                        DeterministicTransition.Action=Some(var,expr);
                    }
                do alreadyCollected.DeterministicTransitions := newEntry::alreadyCollected.DeterministicTransitions.Value
                ()
    

    let transformToGraph (pgm:Stm) : CollectedInformation=
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
            {
                CollectedInformation.InitialState = initialState;
                CollectedInformation.EndState = endState;
                CollectedInformation.States = ref [initialState;endState];
                CollectedInformation.StochasticTransitions = ref [];
                CollectedInformation.IndeterministicTransitions = ref [];
                CollectedInformation.DeterministicTransitions = ref [];
                CollectedInformation.UniqueStateIdGenerator = uniqueStateIdGenerator;
            }
        do collectStatesAndTransitions initialCollectedInformation (initialState,endState) (pgm)
        initialCollectedInformation

    open SafetySharp.GraphVizDot.DotAst
    
    let exportCollectedInformation (collectedInformation:CollectedInformation) : Digraph =
        let stateToNodeMap : Map<State,Node> =
            let stateToNode (state:State) : Node =
                let nodeName = match state.StateId with | StateId(number) -> sprintf "state%d" number
                nodeName
            collectedInformation.States.Value |> List.map (fun state -> (state,stateToNode state)) |> Map.ofList
            
        let exportDeterministicTransition (transition:DeterministicTransition) : TransitionDecl list=
            let exportTransition = 
                {
                    TransitionDecl.From = stateToNodeMap.Item transition.FromState;
                    TransitionDecl.To = stateToNodeMap.Item transition.ToState;
                    TransitionDecl.Attributes = [];
                }
            [exportTransition]

        let exportIndeterministicTransition (transition:IndeterministicTransition) : TransitionDecl list=
            let exportTransition (toState:State) = 
                {
                    TransitionDecl.From = stateToNodeMap.Item transition.FromState;
                    TransitionDecl.To = stateToNodeMap.Item toState;
                    TransitionDecl.Attributes = [];
                }
            transition.ToStates |> List.map exportTransition

        let exportStochasticTransition (transition:StochasticTransition) : (TransitionDecl list*Node)= //exports the virtual node
            let virtualNodeName =  match transition.FromState.StateId with | StateId(number) -> sprintf "state%dstosplit" number // for better design
            let exportTransition (transitionNumber,expr,toState:State) = 
                {
                    TransitionDecl.From = virtualNodeName;
                    TransitionDecl.To = stateToNodeMap.Item toState;
                    TransitionDecl.Attributes = [Attribute.Style(Style.Dashed)];
                }                
            let toVirtualNode =
                {
                    TransitionDecl.From = stateToNodeMap.Item transition.FromState;
                    TransitionDecl.To = virtualNodeName;
                    TransitionDecl.Attributes = [Attribute.Direction(Direction.None)];
                }
            let fromVirtualNode = transition.ToStates |> List.map exportTransition
            ((toVirtualNode::fromVirtualNode),virtualNodeName)
        
        let deterministicTransitions = collectedInformation.DeterministicTransitions.Value |> List.collect exportDeterministicTransition
        let indeterministicTransitions = collectedInformation.IndeterministicTransitions.Value |> List.collect exportIndeterministicTransition
        let (stochasticTransitionss,virtualStochasticNodes) =
            collectedInformation.StochasticTransitions.Value |> List.map exportStochasticTransition |> List.unzip
        let stochasticTransitions = stochasticTransitionss |> List.collect id
        
        let mainGroupWithTransitions =
            {
                Group.NodeAttributes = [];
                Group.Nodes = [];
                Group.Transitions = deterministicTransitions @ indeterministicTransitions @ stochasticTransitions;
            }

        {
            Digraph.Name = "transformedGraph";
            Digraph.GraphAttributes = [];
            Digraph.MainGroup = mainGroupWithTransitions;
            Digraph.SubGroups = [];
        }

    let exportModel (pgm:Pgm) : Digraph =
        pgm.Body |> transformToGraph |> exportCollectedInformation

    let hideExprs = id
    let hideActions = id

    open SafetySharp.Workflow

    let exportModelWorkflow () 
            : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,Digraph> = workflow {
        let! pgm = getState ()
        let asString = exportModel (pgm.Pgm)
        do! updateState asString
    }
