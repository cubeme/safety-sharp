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

module internal VcPassiveFormGCFK09 =
    open SafetySharp.Models.SamHelpers
    open VcSam
    
    type Cache =
        {
            ReadVersion : Map<int,Map<Var,int>> // Node to [Var to ReadVersionNumber]
            WriteVersion : Map<int,Map<Var,int>> // Node to [Var to WriteVersionNumber]
            MaxWriteOfPredecessor : Map<Var,int> // Var to MaxWriteOfPredecessorOfVar
        }
            with
                static member initial =
                    {
                        Cache.ReadVersion = Map.empty<int,Map<Var,int>>;
                        Cache.WriteVersion = Map.empty<int,Map<Var,int>>;
                        Cache.MaxWriteOfPredecessor = Map.empty<Var,int>;
                    }
    
    let rec setReadAndWriteNumber (sigma:Cache) (stm:Stm) : Cache =
        match stm with
            | Stm.Assert (sid,expr) ->
                let sid = sid.Value
                let maxRead = sigma.MaxWriteOfPredecessor
                let maxWrite = sigma.MaxWriteOfPredecessor
                let newSigma =
                    { sigma with
                        Cache.ReadVersion = sigma.ReadVersion.Add(sid,maxRead);
                        Cache.WriteVersion = sigma.WriteVersion.Add(sid,maxWrite);
                    }
                newSigma
            | Stm.Assume (sid,expr) ->
                let sid = sid.Value
                let maxRead = sigma.MaxWriteOfPredecessor
                let maxWrite = sigma.MaxWriteOfPredecessor
                let newSigma =
                    { sigma with
                        Cache.ReadVersion = sigma.ReadVersion.Add(sid,maxRead);
                        Cache.WriteVersion = sigma.WriteVersion.Add(sid,maxWrite);
                    }
                newSigma
            | Stm.Write (sid,variable,expression) ->
                let sid = sid.Value
                let maxRead = sigma.MaxWriteOfPredecessor
                let maxWrite =
                    if sigma.MaxWriteOfPredecessor.ContainsKey variable then
                        let oldVersion = sigma.MaxWriteOfPredecessor.Item variable
                        sigma.MaxWriteOfPredecessor.Add(variable,oldVersion+1)
                    else
                        sigma.MaxWriteOfPredecessor.Add(variable,1) // first time written to variable
                let newSigma =
                    { sigma with
                        Cache.ReadVersion = sigma.ReadVersion.Add(sid,maxRead);
                        Cache.WriteVersion = sigma.WriteVersion.Add(sid,maxWrite);
                        Cache.MaxWriteOfPredecessor = maxWrite
                    }
                newSigma
            | Stm.Block (sid,statements) ->
                let sid = sid.Value
                let newSigmaAfterStatements =
                    List.fold setReadAndWriteNumber sigma statements                
                let maxRead = newSigmaAfterStatements.MaxWriteOfPredecessor
                let maxWrite = newSigmaAfterStatements.MaxWriteOfPredecessor
                let newSigma =
                    { newSigmaAfterStatements with
                        Cache.ReadVersion = sigma.ReadVersion.Add(sid,maxRead);
                        Cache.WriteVersion = sigma.WriteVersion.Add(sid,maxWrite);
                    }
                newSigma
            | Stm.Choice (sid,choices) ->
                let sid = sid.Value       
                let newSigmas =
                    choices |> List.map (setReadAndWriteNumber sigma)                    
                let newReadVersion =
                    newSigmas |> List.collect (fun (sigma:Cache) -> sigma.ReadVersion |> Map.toList)
                let newWriteVersion =
                    newSigmas |> List.collect (fun (sigma:Cache) -> sigma.WriteVersion |> Map.toList)
                let newMaxWrite =
                    let addToMapIfValueHigher (entries:Map<Var,int>) (_var:Var,version:int) : Map<Var,int> =
                        if (entries.ContainsKey _var) && (entries.Item _var >= version) then
                            entries
                        else
                            entries.Add(_var,version)
                    newSigmas |> List.collect (fun (sigma:Cache) -> sigma.MaxWriteOfPredecessor |> Map.toList)
                              |> List.fold addToMapIfValueHigher Map.empty<Var,int>
                let newSigma =
                    { sigma with
                        Cache.ReadVersion = newReadVersion |> Map.ofList |> Map.add sid (sigma.MaxWriteOfPredecessor) // read of the old sigma!
                        Cache.WriteVersion = newWriteVersion |> Map.ofList |> Map.add sid newMaxWrite
                        Cache.MaxWriteOfPredecessor = newMaxWrite
                    }
                newSigma

    
    // TODO: Graph transformation

    // TODO: Local optimizations of [GCFK09], which decrease the number of copies. (Proposed in this paper)    
    // TODO: My own optimization which tries to create only as many variables as necessary for each _type_.

