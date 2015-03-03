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

module internal SamWorkflow =
    open SafetySharp.Workflow

    type ISamModel<'state> =
        interface
            abstract getModel : Sam.Pgm
            abstract setModel : Sam.Pgm -> 'state
        end
        
        
    let getModel<'state when 'state :> ISamModel<'state>> : WorkflowFunction<'state,'state,Sam.Pgm> = workflow {
        let! state = getState
        let model = state.getModel
        return model
    }
    
    let setModel<'state when 'state :> ISamModel<'state>> (model:Sam.Pgm) : WorkflowFunction<'state,'state,unit> = workflow {
        let! state = getState
        let newState = state.setModel model
        do! updateState newState
    }

    type PlainSamModel(model:Sam.Pgm) =
        class end
            with
                member this.getModel : Sam.Pgm = model
                interface ISamModel<PlainSamModel> with
                    member this.getModel : Sam.Pgm = model
                    member this.setModel (model:Sam.Pgm) = PlainSamModel(model)
    
    type PlainScmModelWorkflowState = WorkflowState<PlainSamModel>
    type PlainScmModelWorkflowFunction<'returnType> = WorkflowFunction<PlainSamModel,PlainSamModel,'returnType>

    let createPlainScmWorkFlowState (model:Sam.Pgm) : PlainScmModelWorkflowState =
        WorkflowState<PlainSamModel>.stateInit (PlainSamModel(model))
    
    let setPlainModelState (model:Sam.Pgm) = workflow {
        do! updateState (PlainSamModel(model))
    }
    
    let toPlainModelState<'state when 'state :> ISamModel<'state>> : WorkflowFunction<'state,PlainSamModel,unit> = workflow {
        let! state = getState
        do! setPlainModelState state.getModel
    }