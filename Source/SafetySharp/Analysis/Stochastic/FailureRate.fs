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


namespace SafetySharp.Analysis.Stochastic

open SafetySharp.Analysis

// TODO: Maybe rename to "TransformationOfDistributions"

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

(*
"Transformation" of a Distribution from discrete <-> continuous is called "Limiting forms"

*)