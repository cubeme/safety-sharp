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

module internal TraceableModel =

    open SafetySharp.Workflow
    
    
    // The model transformation goes from a source model to sink model (e.g. from Scm to NuXmv).
    // It performs several intermediate steps (IS) to achieve this. Every such intermediate step
    // makes a tiny transformation of an intermediate model (IM).
    // As formula "transformed IM = IS (untransformed IM)". Examples of IS:
    //   - leveling SCM up transforms SCM to a flat SCM
    //   - converting a flat scm into sam.
    // Each IM of the model transformation should not only update the model, but also the TracingInfo.
    // The TracingInfo contains several forward maps and backward maps.
    // Forward Maps map from source elements to elements in the model currently processed (current elements).
    // Backward Maps map from current elements to source elements.
    // It is possible to conserve the TracingInfos from anywhere in the workflow and start a new
    // TracingInfo from this point (see function startFreshTracingInfo).
    
    type TracingInfo<'source,'target when 'source : comparison and 'target : comparison> = {
        Forward : Map<'source,'target>;
    }



    let getModel<'model,'source,'target when 'model :> IModel<'target> and 'source : comparison and 'target : comparison>
                    : WorkflowFunction<'model*TracingInfo<'source,'target>,
                                       'model*TracingInfo<'source,'target>,
                                       'model> = workflow {
        let! (model,tracingInfo) = getState
        return model
    }
    
    let setModel<'oldmodel,'newmodel,'source,'target when 'newmodel :> IModel<'target> and 'source : comparison and 'target : comparison>
            (model:'newmodel)
                    : WorkflowFunction<'oldmodel*TracingInfo<'source,'target>,
                                       'newmodel*TracingInfo<'source,'target>,
                                       unit> = workflow {
        let! (_,tracingInfo) = getState
        do! updateState (model,tracingInfo)
    }

    // We trace back to the first model of the workflow. The first model has "None" tracingInfo
    let getTracingInfo<'model,'source,'target when 'model :> IModel<'target> and 'source : comparison and 'target : comparison>
                    : WorkflowFunction<'model*TracingInfo<'source,'target>,
                                       'model*TracingInfo<'source,'target>,
                                       TracingInfo<'source,'target>> = workflow {
        let! (model,tracingInfo) = getState
        return tracingInfo
    }

    // to facilitate the porting to model with tracinginfo
    let removeTracingInfo<'model,'source,'target when 'model :> IModel<'target> and 'source : comparison and 'target : comparison>
                    : WorkflowFunction<'model*TracingInfo<'source,'target>,
                                       'model,
                                       unit> = workflow {
        let! (model,tracingInfo) = getState
        do! updateState model
        return ()
    }
    

    let addTracingInfos<'model,'var when 'model :> IModel<'var> and 'var : comparison>
                    : WorkflowFunction<'model,
                                       'model*TracingInfo<'var,'var>,
                                       unit> = workflow {
        let! model = getState
        let variables = model.getStateVars
        let reflexiveVarMap = variables |> List.map (fun var -> var,var) |> Map.ofList
        let tracingInfos =
            {
                TracingInfo.Forward = reflexiveVarMap;
            }
        do! updateState (model,tracingInfos)
    }
        
    
    // a generic example what each transformation needs to do
    let applyIntermediateMapping_ForwardVariables<'source,'untransformed,'transformed when 'source : comparison
                                                                                      and 'untransformed : comparison
                                                                                      and 'transformed : comparison>
            (currentMapping:Map<'source,'untransformed>)
            (intermediateMapping:Map<'untransformed,'transformed>)
                : Map<'source,'transformed> =   // returns updatedMapping
        currentMapping |> Map.filter (fun key value-> intermediateMapping.ContainsKey value)
                       |> Map.map (fun key value -> intermediateMapping.Item value)
    
    // Note:
    //    Making the transformations directly to 'source requires _every_ function to be a generic function
    //    which depends on the source type. E.g.:
    //        let createEmptySteps<'source when 'source : comparison> : PlainScmModelWorkflowFunction<unit> = workflow { }
    //    This is nasty. Either we need a fixed source or another solution.
    //    We introduce tworkflow (traceable workflow). It is done by collecting the TraceInfo-transformation-functions. These
    //    have the needed maps in their closure.
    //    Another idea is to lose the type information and cast everything into a ITraceable
    //    
    //        type ListElement<'a> = int*'a
    //        let moda (b:ListElement<_>) =
    //            let (l,_) = b
    //            l
    
    
    // TODO: This function is used to split the TracingInfo during a workflow (conserve the current TracingInfo start a new one).
    // Thus, this function creates a new TracingInfo with a new source model.
    // E.g:
    //   workflow {
    //       do! readModelA
    //       // now a fresh TracingInfo started. It was created by readModelA
    //       do! transformAtoB
    //       do! transformBtoC
    //       let! tracingInfoAtoC = startFreshTracingInfo
    //       // now a fresh TracingInfo started
    //       let! transformCtoD
    //       let! transformDtoE
    //       let! tracingInfoCtoE = startFreshTracingInfo
    //       // now a fresh TracingInfo started
    //       do! mergeTracingInfoMany [tracingInfoAtoC;tracingInfoCtoE]
    //       // now TracingInfo goes form A to E again
    //   }
    //let startFreshTracingInfo = 



    // Note:
    //   This approach here only works, if the new map can easily be generated. If more sophisticated
    //   transformations are needed, it is better to implement an approach with a "TracingInfoBuilder".
    //   This type does not save the resulting maps itself, but saves a function, which performs the remapping.
    //   These functions can be chained (see FParsec).
    //   Every IS should not perform the remapping itself, update the TracingInfoBuilder.
    //   Example with "traceForwardFromSource":
    //   It needs to provide a new function "traceForwardFromSource" which can be gained by
    //   appending the "traceForwardFromSource<'source,'untransformed>" in TracingInfoBuilder of the current state
    //   to its own "traceForwardIntermediate"<'untransformed,'transformed>. 
    //   "let newForward <'source,'transformed> = (traceForwardFromSource<'source,'untransformed> >>= traceForwardIntermediate<'untransformed,'transformed>".
    //   The function "traceForwardIntermediate" should contain the forwarding map
    //   (Map<'untransformed,'untransformed>) in its closure.
    //   type TraceVariableForwardFunction<'source,'transformed> = 'source -> 'transformed
    //       type TracingInfoBuilder<'source,'target when 'source : comparison and 'target : comparison> = {
    //           ForwardStateVariablesFunction : 'source -> 'target ;
    //       }
    //           with
    //               member this.generateTracingInfo (sourceVariables:'source list) : TracingInfo<'source,'target> =
    //                   {
    //                       TracingInfo.ForwardStateVariables =
    //                           sourceVariables |> List.map (fun var -> (var,this.ForwardStateVariablesFunction var) ) |> Map.ofList
    //                   }
    //       
    //       let applyTracingInfoBuilder<'source,'untransformed,'transformed when 'source : comparison
    //                                                                        and 'untransformed : comparison
    //                                                                        and 'transformed : comparison>
    //               (currentFunction: 'source -> 'untransformed)
    //               (intermediateFunction: 'untransformed' -> 'transformed )
    //                   : ('source -> 'transformed) =   // returns updatedMapping
    //           let newFunction (var:'source) : 'transformed =
    //               let transformation1 = currentFunction var
    //               let transformation2 = intermediateFunction transformation1
    //               transformation2
    //           newFunction

