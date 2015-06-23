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

namespace SafetySharp.ExternalTools

module SmvModels =

    let ``incomplete-case-distinction`` = "incomplete-case-distinction.smv"
    let ``incomplete-instantiation`` = "incomplete-instantiation.smv"        
    let ``not-fully-defined1`` = "not-fully-defined1.smv"
    let ``not-fully-defined2`` = "not-fully-defined2.smv"
    let ``fully-defined`` = "fully-defined.smv"                
    let ``wrong-syntax1`` = "wrong-syntax1.smv"
    let ``wrong-syntax2`` = "wrong-syntax2.smv"
    let ``simple-indeterministic`` = "simple-indeterministic.smv"
    let ``range-not-respected`` = "range-not-respected.smv"
    let ``simple-deterministic`` = "simple-deterministic.smv"
    let ``simple-deterministic-int`` = "simple-deterministic-int.smv"
    let ``simple-inputvariable`` = "simple-inputvariable.smv"
    let ``simple-inputvariable2`` = "simple-inputvariable2.smv"
    let ``simple-combinatorial`` = "simple-combinatorial.smv"
    let ``simple-constants`` = "simple-constants.smv"              
              
    let smvModels = 
        [
        ``incomplete-case-distinction``;
        ``incomplete-instantiation``;
        ``not-fully-defined1``;
        ``not-fully-defined2``;
        ``fully-defined``;
        ``wrong-syntax1``;
        ``wrong-syntax2``;
        ``simple-indeterministic``;
        ``range-not-respected``;
        ``simple-deterministic``;
        ``simple-deterministic-int``;
        ``simple-inputvariable``;
        ``simple-inputvariable2``;
        ``simple-combinatorial``;
        ``simple-constants``;
        ]