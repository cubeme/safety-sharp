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
open SafetySharp.Models.Scm


module internal ScmRewriterNormalize =
    open ScmHelpers
    open ScmRewriterBase
    open SafetySharp.Workflow
    open ScmTracer
    
    let createEmptySteps<'state,'traceableOfOrigin when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        let! model = iscmGetModel ()
        let rootComp = match model with | ScmModel(rootComp) -> rootComp
        let emptyStep =
            {
                StepDecl.FaultExpr = None;
                StepDecl.Behavior =
                    {
                        BehaviorDecl.Body = Stm.Block([]);
                        BehaviorDecl.Locals = [];
                    }
                StepDecl.Contract = Contract.None
            }        
        let rec newCompDecl (compDecl:CompDecl) =
            let newSteps =
                if compDecl.Steps = [] then
                    [emptyStep]
                else
                    compDecl.Steps
            let newSubs =
                compDecl.Subs |> List.map newCompDecl
            { compDecl with
                CompDecl.Steps = newSteps;
                CompDecl.Subs = newSubs
            }
        do! iscmSetModel (ScmModel(newCompDecl rootComp))
    }
    
    let normalize<'state,'traceableOfOrigin when 'state :> IScmTracer<'traceableOfOrigin,'state>> () : IScmTracerWorkflowFunction<'state,'traceableOfOrigin,unit> = workflow {
        do! createEmptySteps ()
    }