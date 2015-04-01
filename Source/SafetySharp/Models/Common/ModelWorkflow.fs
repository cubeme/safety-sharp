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

module internal ModelWorkflow =

    open SafetySharp.Workflow

    let getModel<'model,'trackinginfo when 'model :> IModel and 'trackinginfo :> ITrackingInfo>
                    : WorkflowFunction<'model*('trackinginfo option),'model*('trackinginfo option),'model> = workflow {
        let! (model,trackingInfo) = getState
        return model
    }


    // We track back to the first model of the workflow. The first model has "None" trackingInfo
    let getTrackingInfo<'model,'trackinginfo when 'model :> IModel and 'trackinginfo :> ITrackingInfo>
                    : WorkflowFunction<'model*('trackinginfo option),'model*('trackinginfo option),'trackinginfo option> = workflow {
        let! (model,trackingInfo) = getState
        return trackingInfo
    }
    
    // The transformation of a model goes from source to sink (e.g. from Scm to NuXmv).
    // It has several intermediate steps. Every such step transforms from untransformed to transformed.
    // e.g.:
    //   - leveling SCM up transforms SCM to a flat SCM
    //   - converting a flat scm into sam.
    // Every intermediate transformation should also provide a function, which provides a transformation 

    // Each step for model transformation should not only update the model, but also the TrackingInfo.
    // It needs to provide a new function "trackForwardFromSource" which it can gain by
    // appending the old "trackForwardFromSource<'source,'untransformed>" to
    // its own "trackForwardIntermediate"<'untransformed,'transformed>. 
    // "trackForwardFromSource >>= trackForwardIntermediate" should be <'source,'transformed>.
    // The function "trackForwardIntermediate" should contain the forwarding map
    // (Map<'untransformed,'untransformed>) in its closure.
    
    type TrackVariableForwardFunction<'source,'transformed> = 'source -> 'transformed

    type TrackingInfo<'varSource,'varTarget when 'varSource : comparison and 'varTarget : comparison> = {
        ForwardVariables : Map<'varSource,'varTarget>;
    }
        with
            member this.applyIntermediateForward (TrackVariableForwardFunction)
    

    type TrackingInfoBuilder<'source,'sink> = {
    }
        with
            member this.createTrackingInfo (varsToTrack:'source list) =
                //TODO: Create a map which summarizes all infos
                ()

    type TrackingInfoBuilder with
        static member forwardVariable (functionOnLeft:AstToStringStateFunction)
                                      (:AstToStringStateFunction)
                                      (state:AstToStringState) : TrackingInfo =
            let newState = m state
            f newState

    // TODO: This function is used to split the TrackingInfo during a workflow (conserve the current TrackingInfo start a new one)
    // E.g:
    //   workflow {
    //       do! readModelA
    //       // now a fresh TrackingInfo started. It was created by readModelA
    //       do! transformAtoB
    //       do! transformBtoC
    //       let! trackingInfoAtoC = startFreshTrackingInfo
    //       // now a fresh TrackingInfo started
    //       let! transformCtoD
    //       let! transformDtoE
    //       let! trackingInfoCtoE = startFreshTrackingInfo
    //       // now a fresh TrackingInfo started
    //       do! mergeTrackingInfoMany [trackingInfoAtoC;trackingInfoCtoE]
    //       // now TrackingInfo goes form A to E again
    //   }
    //let startFreshTrackingInfo = 



