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
                    : WorkflowFunction<'model*'trackinginfo,'model*'trackinginfo,'model> = workflow {
        let! (model,trackingInfo) = getState
        return model
    }


    // We track back to the first model of the workflow. The first model has "None" trackingInfo
    let getTrackingInfo<'model,'trackinginfo when 'model :> IModel and 'trackinginfo :> ITrackingInfo>
                    : WorkflowFunction<'model*'trackinginfo,'model*'trackinginfo,'trackinginfo> = workflow {
        let! (model,trackingInfo) = getState
        return trackingInfo
    }

    // to facilitate the porting to model with trackinginfo
    let removeTrackingInfo<'model,'trackinginfo when 'model :> IModel and 'trackinginfo :> ITrackingInfo>
                    : WorkflowFunction<'model*'trackinginfo,'model,unit> = workflow {
        let! (model,trackingInfo) = getState
        do! updateState model
        return ()
    }
    
    // The model transformation goes from a source model to sink model (e.g. from Scm to NuXmv).
    // It performs several intermediate steps (IS) to achieve this. Every such intermediate step
    // makes a tiny transformation of an intermediate model (IM).
    // As formula "transformed IM = IS (untransformed IM)". Examples of IS:
    //   - leveling SCM up transforms SCM to a flat SCM
    //   - converting a flat scm into sam.
    // Each IM of the model transformation should not only update the model, but also the TrackingInfo.
    // The TrackingInfo contains several forward maps and backward maps.
    // Forward Maps map from source elements to elements in the model currently processed (current elements).
    // Backward Maps map from current elements to source elements.
    // It is possible to conserve the TrackingInfos from anywhere in the workflow and start a new
    // TrackingInfo from this point (see function startFreshTrackingInfo).
        
    type TrackVariableForwardFunction<'source,'transformed> = 'source -> 'transformed

    type TrackingInfo<'varSource,'varTarget when 'varSource : comparison and 'varTarget : comparison> = {
        ForwardVariables : Map<'varSource,'varTarget>;
    }
        with
            member this.applyIntermediateForward (TrackVariableForwardFunction) = ()
    

    // TODO: This function is used to split the TrackingInfo during a workflow (conserve the current TrackingInfo start a new one).
    // Thus, this function creates a new TrackingInfo with a new source model.
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

    // Note:
    //   This approach here only works, if the new map can easily be generated. If more sophisticated
    //   transformations are needed, it is better to implement an approach with a "TrackingInfoBuilder".
    //   This type does not safe the resulting maps itself, but safes a function, which performs the remapping.
    //   These functions can be chained (see FParsec).
    //   Every IS should not perform the remapping itself, update the TrackingInfoBuilder.
    //   Example with "trackForwardFromSource":
    //   It needs to provide a new function "trackForwardFromSource" which it can be gained by
    //   appending the "trackForwardFromSource<'source,'untransformed>" in TrackingInfoBuilder of the current state
    //   to its own "trackForwardIntermediate"<'untransformed,'transformed>. 
    //   "let newForward <'source,'transformed> = (trackForwardFromSource<'source,'untransformed> >>= trackForwardIntermediate<'untransformed,'transformed>".
    //   The function "trackForwardIntermediate" should contain the forwarding map
    //   (Map<'untransformed,'untransformed>) in its closure.

