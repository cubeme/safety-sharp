﻿// The MIT License (MIT)
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

namespace SafetySharp.Analysis.VerificationCondition

// Preamble
// A passive form of a SAM-Model is a model which makes for every variable _at most one_ assignment. In those cases
// the assignment "x:=E" can be replaced by a simple assertion "assert x=E".
// The passive form allows the creation of verification condition algorithms which avoid an exponential size of these verification conditions.
// The paper
//  * [FS01] Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions.
//                http://dx.doi.org/10.1145/360204.360220
// introduced this passive form, which is very related to the "static single assignment form" (SSA form) or the "dynamic single assignment form" (DSA form) used in
// compiler optimization. They are essentially the same but do not handle indeterministic guarded commands.
// The paper
//  *  [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904
// describes two transformations to passive form. We implement the proposed one, which is version-optimal (has the least possible
// number of fresh variables for each old variable).


// Implementation of
//  *  [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904

// Advantage of this al
// Disadvantages of this algorithm:

module VcPassiveFormGCFK09 =
    
    // TODO: Graph transformation

    let rec passify = ""

    
    // TODO: Local optimizations of [GCFK09], which decrease the number of copies. (Proposed in this paper)    
    // TODO: My own optimization which tries to create only as many variables as necessary for each _type_.

