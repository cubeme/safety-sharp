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

namespace SafetySharp.Tests.Modelchecking.Prism.PrismInterpretResultTests


open NUnit.Framework
open SafetySharp.Tests
open SafetySharp.Tests.Modelchecking
open SafetySharp
open SafetySharp.Analysis.Modelchecking
open SafetySharp.Analysis.Modelchecking.Prism


[<TestFixture>]
module PrismInterpretResultTests =

    let verificationResult = """
Model checking: P>0.1 [ F s=7&d=x ]
Property constants: x=1

Prob0: 4 iterations in 0.00 seconds (average 0.000000, setup 0.00)

Prob1: 3 iterations in 0.00 seconds (average 0.000000, setup 0.00)

yes = 1, no = 9, maybe = 3

Computing remaining probabilities...
Engine: Hybrid

Building hybrid MTBDD matrix... [levels=6, nodes=30] [1.4 KB]
Adding explicit sparse matrices... [levels=6, num=1, compact] [0.0 KB]
Creating vector for diagonals... [dist=1, compact] [0.0 KB]
Creating vector for RHS... [dist=2, compact] [0.0 KB]
Allocating iteration vectors... [2 x 0.1 KB]
TOTAL: [1.7 KB]

Starting iterations...

Jacobi: 22 iterations in 0.00 seconds (average 0.000000, setup 0.00)

Probabilities (non-zero only) for all states:
0:(0,0)=0.16666650772094727
1:(1,0)=0.33333325386047363
3:(3,0)=0.6666665077209473
7:(7,1)=1.0

Number of states satisfying P>0.1 [ F s=7&d=x ]: 4

Property satisfied in 1 of 1 initial states.

Time for model checking: 0.008 seconds.

Result: true (property satisfied in the initial state)

"""

    [<Test>]
    let ``Regex returns correct result`` () =
        let result = PrismInterpretResult.parseVerificationLog verificationResult
        result.Property =? "P>0.1 [ F s=7&d=x ]"
        result.Result =? PrismVerificationResult.True
        let (constantx,constantxvalue) = result.Constants.Head
        constantx =? "x"
        constantxvalue =? "1"
        ()
        