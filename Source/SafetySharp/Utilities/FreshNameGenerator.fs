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

namespace SafetySharp

module internal FreshNameGenerator =

    let namegenerator_donothing = (fun takenNames based_on -> based_on);


    let namegenerator_c_like (takenNames:Set<string>) (based_on:string) : string =
        // * https://msdn.microsoft.com/en-us/library/e7f8y25b.aspx
        // * Rule-Type: [a-zA-Z_][a-zA-Z0-9_]* without forbidden names (keywords)
        // * note: omit start with 2 underscores
        // * max length of identifier 31 (ansi) or 247 (microsoft). let's stay with 31
        // try to find a real short name (around 20 characters)
        let isContinueCharValid (char:char) :bool =
            ((char >= 'A' && char <= 'Z')||(char >= 'a' && char <= 'z')||(char >= '0' && char <= '9')||char='_')
        //let isStartCharValid (char:char) :bool =
        //    ((char >= 'A' && char <= 'Z')||(char >= 'a' && char <= 'z')||char='_')
        
        // 1. replace invalidChars with '_'
        let nameStep1 = based_on |> String.map ( fun char -> if isContinueCharValid char then char else '_')
        // 2. trim
        let nameStep2 = if nameStep1.Length>20 then nameStep1.Remove 20 else nameStep1
        // 3. add prefix (to avoid name clashes and empty char and starting with 2 '_' or start with a number)
        let nameStep3 = "v"+nameStep2
        // 4. add suffix (when necessary)
        let nameStep4 = 
            let existsName (nameCandidate:string) : bool =
                takenNames.Contains nameCandidate
            let rec inventName numberSuffix : string =
                // If desired name does not exist, get name with the lowest numberSuffix.
                // This is not really beautiful, but finally leads to a free name, (because domain is finite).
                let nameCandidate = sprintf "%s_art%i" nameStep3 numberSuffix
                if existsName nameCandidate = false then
                    nameCandidate
                else
                    inventName (numberSuffix+1)
            if existsName nameStep3 = false then
                nameStep3
            else
                inventName 0
        nameStep4