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

// TODO: Move content into own files "DiscreteDistributions" "ContinuousDistributions" and "TransformationOfDistributions"

(*

A failure rate is xxx (see Fault Tree Handbook page X-25)
The failure rate can change during the life span of the system.
Example "Bathtub Curve" (Fault Tree Handbook page X-24):
 - Burn-In Period:
    In the beginning of the lifespan,
    Can be modeled with the Weibull Distribution
 - Useful Life Period:
    Constant Failure Rate
    In the middle of the lifespan,
    Can be modeled with the Exponential Distribution
 - Wear-Out Process:
    Consequence of Aging
    Can be modeled with the Normal Distribution
*)

(* continuous distributions *)

type RayleighDistribution () =
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
        // time point is 0 (see comment 10.28 of "Bolze, Werner: Grundlagen der Stochastik")
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


type ExponentialDistribution () = 
    // Described in FTH and 
    // Transformation to DTMC given in "Safety Critical Computer Systems" page 186
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

(* discrete distributions *)

(*
"Transformation" of a Distribution from discrete <-> continuous is called "Limiting forms"

*)