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

namespace SafetySharp.Modelchecking.NuXmv


open SafetySharp.Modelchecking

type WriteOnceStatement = SimpleStatement

// contains information, which Decicions have already been taken in the current statement
// - if an assignment is done, write it to a new variable (an artificial field), if it is not the last assignment to this variable
// - keep track, "SimpleGlobalField name" -> "SimpleGlobalField artificial/current"
// first implementation:
// - really unoptimized: each time a variable is written to, a new artifical variable is instanced with the assignment
// - keep state in a WriteOnceTypeArtificialCacheType with functions "setAssignment" "popDecision" "pushDecision" "getCurrentAssignment"
// - after everything is done, make a "next(state of actual x)=next(last artificial x belonging to actual x)"
// optimizations:
// - 1. recursively: when afterwards a variable is not read/written, throw it out
// - 2. maybe use idea of students in a thesis. Pool of ideas: Compiler
// - 3. different algorithm on basis of wp-calculus
// - 4. use simplifier of z3 (also appliable on result of 3)
// - 5. try to use many defines in model checker or exculde artificial fields from state

// One cache is valid for one sequence. Thus if a partition should be transformed, keep in mind, that its update
// needs to be transformed with one cache. Otherwise the bindings or the updates work on outdated data (the
// current value of a binding might depend on the result of an update)

// Current problem: SimpleExpressions also need to be rewritten. Expressions also need to be able to refer to artificial fields.
// - Solution 1: Introduce artifical fields in Simplified Metamodel, refactor SimpleExpression and SimpleStatement. WriteOnceStatement/Metamodel is only a restricted version of Statement. Simplified Metamodel could introduce a check "IsWriteOnce" and contain a "ToWriteOnce"-Member
// - Solution 2: Let WriteOnceType be something on its own. A field could be Artificial

(*
type WriteOnceTypeArtificialCacheType = {
} with
    member this.makeAssignment =
        ""
    member this.popDecision =
        ""
    member this.pushDecision =
        ""
    member this.getCurrentAssignment =
        ""
    member this.getCurrentDecisionsAsSimpleExpression =
        ""

        
type SimpleStatementsToWriteOnceStatements =

    member this.simpleStatementToWriteOnceStatementsCached (stmnts:SimpleStatement list) : WriteOnceStatement list =
        //this
    
    member this.simpleStatementToWriteOnceStatements (stmnts:SimpleStatement list) : WriteOnceStatement list =
        //TODO: Description and Implementation
        stmnts
*)