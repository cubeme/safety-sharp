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

module internal Spg =
    // Safety Program Graph or Stochastic Program Graph
    open SafetySharp
    
    type Var = Tsam.Var
    type Expr = Tsam.Expr
    type VarDecl = Tsam.GlobalVarDecl
    
    type StateId = StateId of int
    
    type State = {
        Label : string;
        StateId : StateId;
    }

    type Action = Var*Expr
    
    type StochasticOption = {
        Number:int;
        Probability:Expr;
        Action:Action option;
        ToState:State;
    }

    type StochasticTransition = {
        Label:string;
        FromState:State;
        Guard:Expr option;
        Options:StochasticOption list;
    }
    
    type DeterministicTransition = {
        Label:string;
        FromState:State;
        Guard:Expr option;
        Action:Action option;
        ToState:State;
    }

    type StochasticProgramGraph = {
        Variables : VarDecl list;
        States : Set<State>;
        InitialState : State;
        //EndOfLoopStates : Set<State>;
        StochasticTransitions : Set<StochasticTransition>;
        DeterministicTransitions : Set<DeterministicTransition>;
        UniqueStateIdGenerator : unit -> StateId;
    }
        with
            static member initial (variables:VarDecl list) (states:Set<State>) (initialState : State) (uniqueStateIdGenerator : unit -> StateId) = 
                {
                    StochasticProgramGraph.Variables = variables;
                    StochasticProgramGraph.States = states;
                    StochasticProgramGraph.InitialState = initialState;
                    StochasticProgramGraph.StochasticTransitions = Set.empty<StochasticTransition>;
                    StochasticProgramGraph.DeterministicTransitions = Set.empty<DeterministicTransition>;
                    StochasticProgramGraph.UniqueStateIdGenerator = uniqueStateIdGenerator;
                }
            member this.unionWith (unionWith:StochasticProgramGraph) =
                { this with
                    States = Set.union this.States unionWith.States;
                    StochasticTransitions = Set.union this.StochasticTransitions unionWith.StochasticTransitions;
                    DeterministicTransitions = Set.union this.DeterministicTransitions unionWith.DeterministicTransitions;
                }
            member this.unionWithMany (unionWith:StochasticProgramGraph list) =
                { this with
                    // Keep the InitialState of this
                    // Keep the EndOfLoopStates of this
                    States = Set.unionMany ((this.States) ::(unionWith |> List.map (fun spg -> spg.States)))
                    StochasticTransitions = Set.unionMany ((this.StochasticTransitions) ::(unionWith |> List.map (fun spg -> spg.StochasticTransitions)))
                    DeterministicTransitions = Set.unionMany ((this.DeterministicTransitions) ::(unionWith |> List.map (fun spg -> spg.DeterministicTransitions)))
                }
