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


namespace SafetySharp.Internal.Analysis.Stochastic

open SafetySharp.Internal.Analysis

(* continuous distributions *)

// Literature
//    [SCSS]: Safety Critical Computer Systems
//    [FTH]: Fault Tree Handbook
//    [FTHAA]: Fault Tree Handbook Aerospace Application
//    [BW]: Bolze, Werner: Grundlagen der Stochastik
//    [WikiExp]: http://en.wikipedia.org/wiki/Exponential_distribution
//    [WikiGeo]: http://en.wikipedia.org/wiki/Geometric_distribution

type ExponentialDistribution () = 
    // Field of application in safety analysis:
    //    Reliability(t) = Probability[No occurrences of system failure until point of time t].
    //    Used to determine the reliability of a component when the failure rate of a component is _constant_ 
    //    (i.e. the probability that a component fails in the time period [t,t+c] (where c is a constant)
    //    is independent of the point of time t, memoryless). We denote this constant failure rate with \lambda.
    //    "[...] the majority of reliability analysis is based on an assumption of a constant failure rate"
    //    [SCSS page 165].
    //    "The failure rate of a device is the number of failures within a given period of time" [SCSS page 164].
    // Detailed description in:
    //    Inference of the formula [FTH page X-20]
    //    Transformation to DTMC given in [SCSS page 186]
    //    Mathematical description given in [BW page 106]
    // Relationship to discrete Distribution:
    //    The discrete Geometric Distribution is also memoryless [WikiExp,WikiGeo].
    //    Geometric Distribution converges to Exponential Distribution
    //    see: http://math.stackexchange.com/questions/93098/how-does-a-geometric-distribution-converge-to-an-exponential-distribution
    // Cumulative Distribution Function:
    //    F(t) = Failure(t) = 1 - e^(- \lambda * t) (if t > 0)
    //    Reliability(t) = e^(- \lambda * t) //Also called the Complementary Cumulative Probability in statistical terminology
    // Probability Density Function:
    //    f(t) = \lambda * e^(- \lambda * t)
    // Expected Value of f(t):
    //    1/\lambda (also called Mean Time To Failure or \theta) [SCSS page 165, FTH page X-20, BW page 112]
    // Variance of f(t):
    //    1/(\lambda^2) 
    // Note:
    //    The Exponential Distribution itself only talks about F(t) (cdf) and f(t) (pdf).
    //    F(t) is also not called Failure(t) in general. We do it here, because we have a strong focus on
    //    safety analysis. Thats also the reason we defined here Reliability(t) for convenience.
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
        // PDF: "Probability Density Function"
        // Mathematically f(x) = ... (derivate of F(x))
        // is not equal to probability _at_ time point in a discrete distribution, because
        // in the continuous case the probability is 0
        ""

    member this.calculateProbabilityOfReliableOperationUntilTimePoint (time:PointOfTime) =
        // _until_ time point. Mathematically R(x) = 1 - F(x)...
        ""

    member this.createFormulaForCASMaxima = ""

    member this.createFormulaForRProgramming = ""

    member this.generateDiscreteApproximation (numberOfStatesToApproximate:int) (durationOfOneStep:int) = // : GeometricDistribution =
        ""


(*
type RayleighDistribution () =
    let a = ""
    
type WeibullDistribution () =
    // Field of application:
    // Detailed description in:
    //    ...
    // Note:
    //    parameter
    
    let a = ""


type PoissonDistribution () =
    let a = ""
    
type NormalDistribution () =
    let a = ""

type GammaDistribution () =
    let a = ""
    

type GaussianDistribution = NormalDistribution

type DistributionWithLinearIncreasingFailureRate () =
    let a = ""    

*)