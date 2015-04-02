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
    
    type TracingInfo<'varSource,'varTarget when 'varSource : comparison and 'varTarget : comparison> = {
        ForwardStateVariables : Map<'varSource,'varTarget>;
    }

    let getModel<'model,'varSource,'varTarget when 'model :> IModel<'varTarget> and 'varSource : comparison and 'varTarget : comparison>
                    : WorkflowFunction<'model*TracingInfo<'varSource,'varTarget>,
                                       'model*TracingInfo<'varSource,'varTarget>,
                                       'model> = workflow {
        let! (model,tracingInfo) = getState
        return model
    }


    // We trace back to the first model of the workflow. The first model has "None" tracingInfo
    let getTracingInfo<'model,'varSource,'varTarget when 'model :> IModel<'varTarget> and 'varSource : comparison and 'varTarget : comparison>
                    : WorkflowFunction<'model*TracingInfo<'varSource,'varTarget>,
                                       'model*TracingInfo<'varSource,'varTarget>,
                                       TracingInfo<'varSource,'varTarget>> = workflow {
        let! (model,tracingInfo) = getState
        return tracingInfo
    }

    // to facilitate the porting to model with tracinginfo
    let removeTracingInfo<'model,'varSource,'varTarget when 'model :> IModel<'varTarget> and 'varSource : comparison and 'varTarget : comparison>
                    : WorkflowFunction<'model*TracingInfo<'varSource,'varTarget>,
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
                TracingInfo.ForwardStateVariables = reflexiveVarMap;
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
        currentMapping |> Map.map (fun key value -> intermediateMapping.Item value)

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

