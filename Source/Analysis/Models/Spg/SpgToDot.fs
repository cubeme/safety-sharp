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

module internal SpgToDot =
    open Spg
    open SafetySharp.GraphVizDot.DotAst
        
        
    let exportExpr (expr:Expr) : string =
        let result = TsamToString.exportExpr expr SamToStringHelpers.AstToStringState.initial
        result.ToString().Replace("\r\n","").Replace("\n","")
        
    //let exportStm (stm:Stm) : string =
    //    let result = TsamToString.exportStm stm SamToStringHelpers.AstToStringState.initial
    //    result.ToString().Replace("\r\n","").Replace("\n","")

    let exportElement (element:Element) : string =
        let result = TsamToString.exportElement element SamToStringHelpers.AstToStringState.initial
        result.ToString().Replace("\r\n","").Replace("\n","")
    

    let hideExprs = id
    let hideActions = id

    let exportStochasticProgramGraph (stochasticProgramGraph:StochasticProgramGraph) : Digraph =
        let stateToNodeMap : Map<State,Node> =
            let stateToNode (state:State) : Node =
                let nodeName = match state.StateId with | StateId(number) -> sprintf "state%d" number
                nodeName
            stochasticProgramGraph.States |> Set.toList |> List.map (fun state -> (state,stateToNode state)) |> Map.ofList
            
        let exportDeterministicTransition (transition:DeterministicTransition) : TransitionDecl list =
            let label =
                match (transition.Guard,transition.Action) with
                    | Some(guard),Some(assignTo,assignThis) ->
                        sprintf "%s // %s:=%s" (exportExpr guard) (exportElement assignTo) (exportExpr assignThis)
                    | Some(guard),None ->
                        sprintf "%s" (exportExpr guard)
                    | None,Some(assignTo,assignThis) ->
                        sprintf "// %s:=%s" (exportElement assignTo) (exportExpr assignThis)
                    | None,None ->
                        ""
            let exportTransition = 
                {
                    TransitionDecl.From = stateToNodeMap.Item transition.FromState;
                    TransitionDecl.To = stateToNodeMap.Item transition.ToState;
                    TransitionDecl.Attributes = [Attribute.Label(label)];
                }
            [exportTransition]
            
        let exportStochasticTransition (transition:StochasticTransition) : (TransitionDecl list*Node)= //exports the virtual node1
            let virtualNodeName =  match transition.FromState.StateId with | StateId(number) -> sprintf "state%dstosplit" number // for better design
            let exportOption (option:StochasticOption) =                
                let label =
                    let probabilityLabel = (exportExpr option.Probability)
                    match option.Action with
                        | Some( (assignTo,assignThis) ) ->
                            sprintf "%s // %s:=%s" (probabilityLabel) (exportElement assignTo) (exportExpr assignThis)
                        | None ->
                            probabilityLabel
                {
                    TransitionDecl.From = virtualNodeName;
                    TransitionDecl.To = stateToNodeMap.Item option.ToState;
                    TransitionDecl.Attributes = [Attribute.Style(Style.Dashed);Attribute.Label(label)];
                }                
            let toVirtualNode =
                {
                    TransitionDecl.From = stateToNodeMap.Item transition.FromState;
                    TransitionDecl.To = virtualNodeName;
                    TransitionDecl.Attributes = [Attribute.Direction(Direction.None)];
                }
            let fromVirtualNode = transition.Options |> List.map exportOption
            ((toVirtualNode::fromVirtualNode),virtualNodeName)
        
        let deterministicTransitions = stochasticProgramGraph.DeterministicTransitions |> Set.toList |> List.collect exportDeterministicTransition
        let (stochasticTransitionss,virtualStochasticNodes) =
            stochasticProgramGraph.StochasticTransitions |> Set.toList |> List.map exportStochasticTransition |> List.unzip
        let stochasticTransitions = stochasticTransitionss |> List.collect id
        
        let mainGroupWithTransitions =
            {
                Group.NodeAttributes = [];
                Group.Nodes = [];
                Group.Transitions = deterministicTransitions @ stochasticTransitions;
            }

        {
            Digraph.Name = "transformedGraph";
            Digraph.GraphAttributes = [];
            Digraph.MainGroup = mainGroupWithTransitions;
            Digraph.SubGroups = [];
        }