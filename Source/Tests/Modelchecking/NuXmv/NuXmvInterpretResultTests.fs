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

namespace SafetySharp.Tests.Modelchecking.NuXmv.NuXmvInterpretResultTests

open NUnit.Framework
open SafetySharp.Tests
open SafetySharp.Tests.Modelchecking
open SafetySharp.Internal.Utilities
open SafetySharp.Internal.Modelchecking
open SafetySharp.Internal.Modelchecking.NuXmv


[<TestFixture>]
module NuXmvInterpretResultTests =

    let ``NuXmv Started-ResultStdoutSuccess`` =
        """*** This is nuXmv 1.0.0 (compiled on Wed Feb 19 14:15:37 UTC 2014)
*** Copyright (c) 2014, Fondazione Bruno Kessler

*** For more information on nuXmv see https://nuxmv.fbk.eu
*** or email to <nuxmv@list.fbk.eu>.
*** Please report bugs at https://nuxmv.fbk.eu/bugs
*** (click on "Login Anonymously" to access)
*** Alternatively write to <nuxmv@list.fbk.eu>.

*** This version of nuXmv is linked to NuSMV 2.5.devel.
*** For more information on NuSMV see <http://nusmv.fbk.eu>
*** or email to <nusmv-users@list.fbk.eu>.
*** Copyright (C) 2010-2014, Fondazione Bruno Kessler

*** This version of nuXmv is linked to the CUDD library version 2.4.1
*** Copyright (c) 1995-2004, Regents of the University of Colorado

*** This version of nuXmv is linked to the MiniSat SAT solver. 
*** See http://minisat.se/MiniSat.html
*** Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
*** Copyright (c) 2007-2010, Niklas Sorensson

*** This version of nuXmv is linked to MathSAT
*** Copyright (C) 2014 by Fondazione Bruno Kessler
*** Copyright (C) 2014 by University of Trento
*** See http://mathsat.fbk.eu

"""
    let ``NuXmv Started-ResultStderrSuccess`` = ""
    
    let ``set default_trace_plugin 4-ResultStdoutSuccess`` = ""
    let ``set default_trace_plugin 4-ResultStderrSuccess`` = ""

    let ``read_model -i Modelchecking/NuXmv/testcase1.smv-ResultStdoutSuccess`` = ""
    let ``read_model -i Modelchecking/NuXmv/testcase1.smv-ResultStderrSuccess`` = """Parsing file "Modelchecking/NuXmv/testcase1.smv" ..... done.
"""

    let ``flatten_hierarchy-ResultStdoutSuccess`` = ""
    let ``flatten_hierarchy-ResultStderrSuccess`` =
        """Flattening hierarchy...
...done
"""
    let ``flatten_hierarchy-ResultStderrFailed`` = """Flattening hierarchy...

file Modelchecking/NuXmv/wrong-syntax1.smv: line 3: "booleaan" undefined
Quitting the GR commands... 
Quitting the Automata package... 
Quitting the Mathsat package...
Quitting the Trace_Executor package... 
Quitting the GR package... 
Quitting the Cegar package...
Quitting the Abstraction package...
Quitting the AbsBmc package...
Quitting the QE package...
Quitting the Sym2ex package... 
Quitting the Compass package... 
Quitting the BMC package... 
Done 
Initializing the Compass package... 
Initializing the Mathsat package...
Initializing the Automata package... 
Initializing the Trace_Executor package... 
Initializing the GR package... 
Initializing the QE package...
Initializing the Abstraction package...
Initializing the AbsBmc package...
Initializing the Cegar package...
Initializing the Sym2ex package... 
Initializing the GR commands... 
"""

    let ``encode_variables-ResultStdoutSuccess`` = ""
    let ``encode_variables-ResultStderrSuccess`` =
        """Building variables...
Heuristics "basic" is going to be used to create varordering statically
...done
"""
    let ``encode_variables-ResultStderrFailed1` = """A model must be read before. Use the "read_model" command.
"""

    let ``build_flat_model-ResultStdoutSuccess`` = ""
    let ``build_flat_model-ResultStderrSuccess`` =
        """
The sexp model has been built from file Modelchecking/NuXmv/testcase1.smv.
"""

    let ``build_model-ResultStdoutSuccess`` = ""
    let ``build_model-ResultStderrSuccess`` =
        """
The model has been built from file Modelchecking/NuXmv/testcase1.smv.
"""

    let ``quit-ResultStdoutSuccess`` = ""
    let ``quit-ResultStderrSuccess`` = "Quitting the GR commands... 
Quitting the Automata package... 
Quitting the Mathsat package...
Quitting the Trace_Executor package... 
Quitting the GR package... 
Quitting the Cegar package...
Quitting the Abstraction package...
Quitting the AbsBmc package...
Quitting the QE package...
Quitting the Sym2ex package... 
Quitting the Compass package... 
Quitting the BMC package... 
Done 

Successful termination
"




    [<Test>]
    let ``NuXmv is in PATH or in dependency folder`` () =
        let path = ExecuteNuXmv.FindNuXmv ()
        (path.Length > 0) =? true