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


namespace SafetySharp.Internal.Analysis.Stochastic

open SafetySharp.Internal.Analysis

(* discrete distributions *)

// Literature
//    [SCSS]: Safety Critical Computer Systems
//    [FTH]: Fault Tree Handbook
//    [FTHAA]: Fault Tree Handbook Aerospace Application
//    [BW]: Bolze, Werner: Grundlagen der Stochastik
//    [WikiExp]: http://en.wikipedia.org/wiki/Exponential_distribution
//    [WikiGeo]: http://en.wikipedia.org/wiki/Geometric_distribution

type GeometricDistribution () = 
    // Field of application in safety analysis:
    //    We use the convention "first 'success' (in our case failure) in step number k (for k in 1,2,3,...)
    //    Discrete Model Checkers cannot use Continuous Distributions. So Continuous Distributions have to
    //    be approximated by Discrete Distributions. The mathematical background model of MTTF (Mean
    //    Time To Failure of a safety critical component) is the Continuous Exponential Distribution.
    //    Reliability(t) = Probability[No occurrences of system failure until point of time t].
    //    For further details on MTTF see ContinuousDistributions.fs/ExponentialDistribution.
    // Detailed description in:
    //    Inference of the formula [BW page 57,61]
    // Relationship to continuous Distribution:
    //    The continuous Exponential Distribution is also memoryless [WikiExp,WikiGeo].
    //    http://math.stackexchange.com/questions/93098/how-does-a-geometric-distribution-converge-to-an-exponential-distribution    
    // P (X < k)    (analogue to Cumulative Distribution Function):
    //    P (X >= k) = (1-p)^(k-1)  <--- p is the probability of a failure in one step. This formula says "nothing went wrong in the first k-1 steps, the 'coin' flipped to 'no failure'"
    //    P (X < k) = 1 - P (X >= k) = 1 - (1-p)^(k-1)   <---- This describes the probability of a failure within the first k-1 steps ("something went wrong in the first k-1 steps")
    //    P (X <= k) = P(X < k+1) = 1 - P (X >= k+1) = 1 - (1-p)^k   <---- This describes the probability of a failure within the first k steps ("something went wrong in the first k steps")
    // Probability Mass Function (pmf)    (P (X = k), analogue to Probability Density Function):
    //    P(X = k) = p * (1-p)^(k-1)     <---- a failure occurred exactly in step number k the first time
    // Expected Value of P:
    //    E(X) = 1/p <---- average number of the step, where the first time
    // Variance of P:
    //    V(X) = (1-p)/(p^2)
    // Note:
    //    \Omega\prime = \mathbb{N}. Sample Space are the Natural Numbers.
    //    In the initial state k=0 the probability of an error should be 0
    member this.generateDtmc (numberOfStatesToApproximate:int,durationOfOneStep) =
        // another idea: show graph of quality of approximation
        ""
    
    member this.calculateFailureRate (time:PointOfTime) =
        ""
    member this.calculateTimeToFailure () =
        ""
    member this.calculateProbabilityOfFailureAtTimePoint (time:PointOfTime) =
        // _at_ time point
        // In the continuous case the probability at a specific
        // time point is 0 [BW comment 10.28]
        0        

    member this.calculateProbabilityOfFailureUntilTimePoint (time:PointOfTime) =
        // CDF. "Cumulative Distribution Function"
        // _until_ time point. Mathematically F(x) = ... (integral of f(x)). Sometimes also denoted Q(x)
        ""
        
    member this.calculateDerivateOfProbabilityOfFailureUntilTimePoint (time:PointOfTime) =
        // pdf: "Probability Density Function"
        // Mathematically f(x) = ... (derivate of F(x))
        // is not equal to probability _at_ time point in a discrete distribution, because
        // in the continuous case the probability is 0
        ""

    member this.calculateProbabilityOfReliableOperationUntilTimePoint (time:PointOfTime) =
        // _until_ time point. Mathematically R(x) = 1 - F(x)...
        ""

    member this.createFormulaForCASMaxima = ""

    member this.createFormulaForRProgramming = ""


(*
type BinominalDistribution () =
    let a = "2"

*)