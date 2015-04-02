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

module internal ScmWorkflow =
    open SafetySharp.Workflow
    open Scm
        
    type IScmModel<'state> =
        interface
            inherit IModel<StateVar> 
            abstract getModel : ScmModel
            abstract setModel : ScmModel -> 'state
        end

        
    type IScmModelWithTracing<'state,'source when 'state :> IScmModel<'state> and 'source : comparison> =
        'state * TraceableModel.TracingInfo<'source,StateVar>

    type IScmModelWorkflowFunction<'state,'source,'returnType when 'state :> IScmModel<'state> and 'source : comparison> =
        WorkflowFunction<IScmModelWithTracing<'state,'source>,
                         IScmModelWithTracing<'state,'source>,
                         'returnType>
                
    let getIscmModel<'state when 'state :> IScmModel<'state>> : IScmModelWorkflowFunction<'state,_,_> = workflow {
        let! iscmModel = TraceableModel.getModel
        let model = iscmModel.getModel
        return model
    }    
    
    let setIscmModel<'state when 'state :> IScmModel<'state>> (model:ScmModel) : IScmModelWorkflowFunction<'state,_,_> = workflow {
        let! iscmModel = TraceableModel.getModel
        let newIscmModel = iscmModel.setModel model
        do! TraceableModel.setModel newIscmModel
    }
    
    let getScmModel : WorkflowFunction<Scm.ScmModel,Scm.ScmModel,Scm.ScmModel> = workflow {
        let! model = getState
        return model
    }

    let setScmModel<'oldIrrelevantState> (model:ScmModel) : WorkflowFunction<'oldIrrelevantState,ScmModel,unit> = workflow {
        do! updateState model

    }

    type PlainScmModel(model:ScmModel) =
        class end
            with
                member this.getModel : ScmModel = model
                interface IScmModel<PlainScmModel> with
                    member this.getStateVars =
                        let imodel = this.getModel :> IModel<StateVar>
                        imodel.getStateVars
                    member this.getModel : ScmModel = model
                    member this.setModel (model:ScmModel) = PlainScmModel(model)
    
    type PlainScmModelWithTracing<'source when 'source : comparison> =
        PlainScmModel * TraceableModel.TracingInfo<'source,StateVar>

    type PlainScmModelWorkflowFunction<'returnType,'source when 'source : comparison> =
        WorkflowFunction<PlainScmModelWithTracing<'source>,
                         PlainScmModelWithTracing<'source>,
                         'returnType>
        
    let setPlainModelState (model:ScmModel) = workflow {
        do! updateState (PlainScmModel(model))
    }
    
    let iscmToPlainModelState<'state when 'state :> IScmModel<'state>> : WorkflowFunction<'state,PlainScmModel,unit> = workflow {
        let! state = getState
        do! setPlainModelState state.getModel
    }
    
    let scmToPlainModelState : WorkflowFunction<ScmModel,PlainScmModel,unit> = workflow {
        let! state = getState
        do! setPlainModelState state
    }
        
    let iscmToScmState<'state when 'state :> IScmModel<'state>> : WorkflowFunction<'state,ScmModel,unit> = workflow {
        let! state = getState
        do! SafetySharp.Workflow.updateState state.getModel
    }
    