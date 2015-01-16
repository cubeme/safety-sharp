// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Models.Scm

module internal ScmRewriterConvertDelayedBindings =
    open ScmHelpers
    open ScmRewriterBase
    
    // Idea:
    //   For each delayed binding:
    //     * Check if prov port does not write to a field
    //     * Check that there is no read-Operation on a inout-Parameter/in-Parameter
    //     * Introduce new fields for each inout-Parameter written to
    //     * To the beginning of _all_ steps  ("Pre-Step"), add Call to ProvPort with new artificial parameters
    //     * Remove/Replace the Delayed Binding by an instantaneous.
    //     * Replace the Port Call by a BlockStatement, where each of the inout-Parameter gets assigned to the new Field
    //   Note:
    //     * The ProvPort call may contain a choice. Thus, the content of the artificial fields may not always be
    //       simply an expression depending on pre-Values of Fields. (Example: Guards true/true;
    //       Statements: "field1:=1;field2:=1"/"field1:=2;field2:=2" TODO: Create example file
    //     * Only for the step of the root-component we can guarantee, that nothing happens before the first statement
    //       and nothing after the last. 
    //     * "Pre-Step" must be executed before the step of the root. It is not enough to add it as prefix to all local
    //       steps, because the local step may be executed later by the root step and the environment has been changed before.
    //       TODO: Create an example, where the order makes a difference!!!
    //     * But: We could save the artificial fields in a list. It could give hints for later optimizations.
    //   TODO:
    //     * When are execution in the "Pre-Step" (Note 2) and execution as first statements of a step the same???
    //       Do we expect the former or the latter?
    //     * Difference between making it "Pre-Step" (described here) or "Post-Step" (with better initial values)

        