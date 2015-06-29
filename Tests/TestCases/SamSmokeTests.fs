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

namespace TestCases

module internal SamSmokeTests =
    let smoketestsStochastic = 
        [
         "nestedBlocks2.sam";
        ] |> Seq.map (fun (a) -> [|a|])

        
    let smoketestsDeterministic = 
        [
         "smokeTest1.sam";
         "smokeTest2.sam";
         "smokeTest3.sam";
         "smokeTest4.sam";
         "smokeTest5.sam";
         "smokeTest6.sam";
         "smokeTest7.sam";
         "smokeTest8.sam";
         "smokeTest9.sam";
         "smokeTest10.sam";
         "smokeTest11.sam";
         "smokeTest12.sam";
         "smokeTest13.sam";
         "smokeTest14.sam";
         "smokeTest15.sam";
         "smokeTest16.sam";
         "smokeTest17.sam";
         "smokeTest18.sam";
         "smokeTest19.sam";
         "smokeTest20.sam";
         "smokeTest21.sam";
         "smokeTest22.sam";
         "smokeTest23.sam";
         "smokeTest24.sam";
         "smokeTest25.sam";
         "nestedBlocks1.sam";
         "reservedNames.sam";
         "overflowIntError1.sam";
         "overflowIntError2.sam";
         "overflowIntWrapAround1.sam";
         "overflowIntWrapAround2.sam";
         "overflowIntWrapAround3.sam";
         "overflowIntWrapAround4.sam";
         "overflowIntClamp1.sam";
         "overflowIntClamp2.sam";
        ] |> Seq.map (fun (a) -> [|a|])

    let smoketestsAll =
        Seq.append smoketestsStochastic smoketestsDeterministic

        
    let smokeTestsSatsInjectSamDeterministic =
        [
            "../../Examples/SAM/smokeTest1.sats";
        ] |> Seq.map (fun (a) -> [|a|])