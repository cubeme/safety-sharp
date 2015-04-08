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

module internal ScmRewriterFlattenModel =
    open ScmHelpers
    open ScmRewriterBase
    open ScmRewriterNormalize
    open ScmRewriterLevelUp
    open ScmRewriterConvertFaults
    open ScmRewriterConvertDelayedBindings
    open ScmRewriterInlineBehavior
    open SafetySharp.Workflow
    open ScmWorkflow

    
    // flatten model means
    //  * normalize
    //  * flatten hierarchy
    //  * convert faults
    //  * convert delayed ports
    //  * inline behaviors

    let flattenModel<'oldState when 'oldState :> IScmModel<'oldState>> ()
                        : ExogenousWorkflowFunction<'oldState,PlainScmModel,_,Traceable,Traceable,unit> = workflow {
            /// normalize
            do! normalize ()
            
            // level up everything
            do! levelUpSubcomponentsWrapper ()
            //do! assertNoSubcomponent (assertion is done as last step)
            //do! checkConsistency
            
            // convert faults
            do! convertFaultsWrapper ()
            //do! assertNoFault
            //do! checkConsistency
            
            // convert delayed bindings            
            do! convertDelayedBindingsWrapper ()
            //do! checkConsistency

            // inline everything beginning with the main step
            do! inlineBehaviorsWrapper
            //do! assertNoPortCall
            //do! checkConsistency

            //do! iscmToScmState
            do! iscmToPlainModelState ()
        }


