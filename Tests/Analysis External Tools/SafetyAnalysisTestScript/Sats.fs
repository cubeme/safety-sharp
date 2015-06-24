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

namespace SafetySharp.SafetyAnalysisTestScript

module internal Sats =

    type DoStatement =
        | SetEngineOption of Option:SafetySharp.EngineOptions.IEngineOption
        | SetMainModel of FileName:string
        //| InjectSamModel of FileName:string
        //| InjectLustreModel of FileName:string
        // For reports        
        // | PrintHtmlReport
        // | SetChapterName
        // | SetSectionName
    
    type LetIdentifier = string        

    type LetType =
        | LetTypeDccaResult
        | LetTypePropertyResult
        //| LetTypeSimulationResult
        //| LetTypeProbabiilityResult

    type LetStatement =
        //| AtStepInvariant
        //| AtReachable
        | AtLtlFormula of LetIdentifier:LetIdentifier * Formula:string
        //| AtLtlFormula_withSpin
        //| AtLtlFormula_withNusmv
        //| AtLtlFormula_withNuxmv
        //| AtLtlFormula_withXsap
        //| AtCtlFormula_withNusmv
        | AtDccaLtl of LetIdentifier:LetIdentifier * Hazard:string
        //| AtDccaLtl_withSpin
        //| AtDccaLtl_withNusmv
        //| AtDccaLtl_withNuxmv
        //| AtDccaLtl_withXsap
        //| AtDccaCtl
        //| AtDccaCtl_withNusmv
        //| AtDccaCtl_withNuxmv
        //| AtDccaCtl_withXsap
        //| AtDccaPruning
        //| AtDccaPruning_withSpin
        //| AtDccaPruning_withNusmv
        //| AtDccaPruning_withNuxmv
        //| AtDccaPruning_withXsap
        //| AtDccaPruning_withPrism
        //| AtDccaFastBdd
        //| AtDccaFastBdd_withXsap
        //| AtDccaFastBdd_withInternal
        //| AtOrderedDccaFastBdd
        //| AtOrderedDccaFastBdd_withXsap
        //| AtOrderedDccaFastBdd_withInternal
        //| AtProbabilisticFullModel
        //| AtProbabilisticFullModel_withPrism
        //| AtContract
        //| AtContract_withBoogie
        //| AtContract_withNusmv
        //| AtMethodsCalled
        //| AtMethodsCalled_withNusmv
        //| Simulate
        //| Simulate_withInternal
        //| Simulate_withSpin
        //| Simulate_withNusmv
        //| Simulate_withNuxmv
        //| Simulate_withXsap
        //| Simulate_withPrism
        
    type ExpectStatement =
        | ExpectDccaResult  of LetIdentifier:LetIdentifier * Result:(Set<SafetySharp.Models.ScmHelpers.FaultPath> list)
        | ExpectPropertyResult of LetIdentifier:LetIdentifier * Result:SafetySharp.Ternary.Ternary
        //| ExpectSimulationResult
        //| ExpectProbabiilityResult

    type SatsStatement =
        | DoStatement of DoStatement
        | LetStatement of LetStatement
        | ExpectStatement of ExpectStatement

    type SatsPgm = {
        Pgm : SatsStatement list;
        LetBindings : Map<LetIdentifier,LetType>;
    }