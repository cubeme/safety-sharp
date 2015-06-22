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

namespace SafetySharp.Modelchecking


open NUnit.Framework
open SafetySharp.Modelchecking
open SafetySharp
open SafetySharp.Analysis.Modelchecking
open SafetySharp.Analysis.Modelchecking.PromelaSpin


[<TestFixture>]
module PanInterpretResultTests =

    let verificationResultErrorSelfLoop = """error: proctype 'System' line 14, state 14: has unconditional self-loop

pan: elapsed time 0 seconds
pan could not be started""" //example: smokeTest19.sam

    
    let verificationResultErrorStuck = """pan:1: invalid end state (at depth 0)
pan: wrote smokeTest18.sam.pml.trail

(Spin Version 6.2.7 -- 2 March 2014)
Warning: Search not completed
	+ Partial Order Reduction

Full statespace search for:
	never claim         	- (none specified)
	assertion violations	+
	acceptance   cycles 	- (not selected)
	invalid end states	+

State-vector 16 byte, depth reached 1, errors: 1
        2 states, stored
        0 states, matched
        2 transitions (= stored+matched)
        0 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.000	equivalent memory usage for states (stored*(State-vector + overhead))
    0.153	actual memory usage for states
   64.000	memory used for hash table (-w24)
    0.069	memory used for DFS stack (-m2000)
   64.195	total actual memory usage



pan: elapsed time 0 seconds""" //example smokeTest18.sam

    let verificationResultErrorAssertionViolated1 = """warning: never claim + accept labels requires -a flag to fully verify
warning: for p.o. reduction to be valid the never claim must be stutter-invariant
(never claims generated from LTL formulae are stutter-invariant)
pan:1: end state in claim reached (at depth 3502)
pan: wrote ffb.pml.trail
(Spin Version 6.0.0 -- 5 December 2010)
Warning: Search not completed
	+ Partial Order Reduction
Full statespace search for:
	never claim         	+
	assertion violations	+ (if within scope of claim)
	cycle checks       	- (disabled by -DSAFETY)
	invalid end states	- (disabled by never claim)
State-vector 112 byte, depth reached 3502, ••• errors: 1 •••
      208 states, stored
        0 states, matched
      208 transitions (= stored+matched)
     3087 atomic steps
hash conflicts:         0 (resolved)
    5.247	memory usage (Mbyte)
pan: elapsed time 0.01 seconds"""

    let verificationResultErrorAssertionViolated2 = """pan:1: assertion violated  !((vTank0_0__maxPressure__>=60)) (at depth 13)
pan: wrote verification.pml.trail

(Spin Version 6.2.7 -- 2 March 2014)
Warning: Search not completed
	+ Partial Order Reduction

Full statespace search for:
	never claim         	+ (ltl_0)
	assertion violations	+ (if within scope of claim)
	acceptance   cycles 	- (not selected)
	invalid end states	- (disabled by never claim)

State-vector 52 byte, depth reached 13, errors: 1
        2 states, stored
        0 states, matched
        2 transitions (= stored+matched)
       11 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.000	equivalent memory usage for states (stored*(State-vector + overhead))
    0.138	actual memory usage for states
   64.000	memory used for hash table (-w24)
    0.069	memory used for DFS stack (-m2000)
   64.195	total actual memory usage



pan: elapsed time 0 seconds"""

    let verificationResultSuccess = """
(Spin Version 6.2.7 -- 2 March 2014)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	- (none specified)
	assertion violations	+
	acceptance   cycles 	- (not selected)
	invalid end states	+

State-vector 12 byte, depth reached 1, errors: 0
        2 states, stored
        1 states, matched
        3 transitions (= stored+matched)
        0 atomic steps
hash conflicts:         0 (resolved)

Stats on memory usage (in Megabytes):
    0.000	equivalent memory usage for states (stored*(State-vector + overhead))
    0.154	actual memory usage for states
   64.000	memory used for hash table (-w24)
    0.069	memory used for DFS stack (-m2000)
   64.195	total actual memory usage


unreached in proctype System
	smokeTest1.sam.pml:14, state 10, "-end-"
	(1 of 10 states)

pan: elapsed time 0 seconds""" //example smokeTest1


    let verificationResultMaybe = """error: max search depth too small

(Spin Version 6.2.7 -- 2 March 2014)
	+ Partial Order Reduction

Full statespace search for:
	never claim         	- (none specified)
	assertion violations	+
	acceptance   cycles 	- (not selected)
	invalid end states	+

State-vector 20 byte, depth reached 1999, errors: 0
    80201 states, stored
    79801 states, matched
   160002 transitions (= stored+matched)
   400201 atomic steps
hash conflicts:        94 (resolved)

Stats on memory usage (in Megabytes):
    2.753	equivalent memory usage for states (stored*(State-vector + overhead))
    2.593	actual memory usage for states (compression: 94.18%)
         	state-vector as stored = 18 byte + 16 byte overhead
   64.000	memory used for hash table (-w24)
    0.069	memory used for DFS stack (-m2000)
   66.637	total actual memory usage


unreached in proctype System
	smokeTest16.sam.pml:19, state 10, "vj = (vj+2)"
	smokeTest16.sam.pml:36, state 23, "vj = (vj+256)"
	smokeTest16.sam.pml:45, state 36, "-end-"
	(3 of 36 states)

pan: elapsed time 0.061 seconds
pan: rate 1314770.5 states/second""" //example smokeTest16.sam

    [<Test>]
    let ``Regex returns correct result when verification was successful`` () =
        let result = PanInterpretResult.parseVerificationLog verificationResultSuccess
        result.Errors =? "0"
        result.Result =? PanInterpretResult.PanVerificationResult.True
        ()
        
    [<Test>]
    let ``Regex returns correct result when assertion is violated (Test 1)`` () =
        let result = PanInterpretResult.parseVerificationLog verificationResultErrorAssertionViolated1
        result.Errors =? "1"
        result.Result =? PanInterpretResult.PanVerificationResult.False
        ()
        
    [<Test>]
    let ``Regex returns correct result when assertion is violated (Test 2)`` () =
        let result = PanInterpretResult.parseVerificationLog verificationResultErrorAssertionViolated2
        result.Errors =? "1"
        result.Result =? PanInterpretResult.PanVerificationResult.False
        ()
        
    [<Test>]
    let ``Regex returns correct result when search depth is too small`` () =
        let result = PanInterpretResult.parseVerificationLog verificationResultMaybe
        result.Errors =? "0"
        result.Result =? PanInterpretResult.PanVerificationResult.Maybe
        ()
        
    [<Test>]
    let ``Regex returns correct result when model could not be read`` () =
        let result = PanInterpretResult.parseVerificationLog verificationResultErrorSelfLoop
        result.Errors =? "1"
        result.Result =? PanInterpretResult.PanVerificationResult.Maybe
        ()
                
    [<Test>]
    let ``Regex returns correct result when stuck`` () =
        let result = PanInterpretResult.parseVerificationLog verificationResultErrorStuck
        result.Errors =? "1"
        result.Result =? PanInterpretResult.PanVerificationResult.Maybe
        ()
        