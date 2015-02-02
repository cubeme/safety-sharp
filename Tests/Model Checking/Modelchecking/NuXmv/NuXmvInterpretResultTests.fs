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

namespace SafetySharp.Tests.Modelchecking.NuXmv.NuXmvInterpretResultTests

open NUnit.Framework
open SafetySharp.Tests
open SafetySharp.Tests.Modelchecking
open SafetySharp
open SafetySharp.Analysis.Modelchecking
open SafetySharp.Analysis.Modelchecking.NuXmv


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
    let ``read_model -i Modelchecking/NuXmv/wrong-syntax2.smv-ResultStderrFailed`` =
        """Parsing file "Modelchecking/NuXmv/wrong-syntax2.smv" ..... 
file Modelchecking/NuXmv/wrong-syntax2.smv: line 5: at token "": syntax error
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
    let ``flatten_hierarchy-ResultStdoutFailed`` = ""

    let ``encode_variables-ResultStdoutSuccess`` = ""
    let ``encode_variables-ResultStderrSuccess`` =
        """Building variables...
Heuristics "basic" is going to be used to create varordering statically
...done
"""
    let ``encode_variables-ResultStderrFailed1`` = """A model must be read before. Use the "read_model" command.
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
    let ``quit-ResultStderrSuccess`` = """Quitting the GR commands... 
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
"""

    //not-fully-defined1
    let checkFsmNotTotalWithDeadlockStdout = """
##########################################################
The transition relation is not total. A state without
successors is:
x = FALSE
The transition relation is not deadlock-free.
A deadlock state is:
x = FALSE
##########################################################"""
    
    let checkFsmNotTotalWithDeadlockStderr = """Checking totality and deadlock states.

********   WARNING   ********
Fair states set of the finite state machine is empty.
This might make results of model checking not trustable.
******** END WARNING ********"""

    //not-fully-defined2
    let checkFsmNotTotalWithoutDeadlockStdout = """
##########################################################
The transition relation is not total. A state without
successors is:
x = FALSE
However, all the states without successors are
non-reachable, so the machine is deadlock-free.
##########################################################"""

    let checkFsmNotTotalWithoutDeadlockStderr = """Checking totality and deadlock states.
"""

    //fully-defined
    let checkFsmTotalStdout = """
##########################################################
The transition relation is total: No deadlock state exists
##########################################################
"""
    let checkFsmTotalStderr = """Checking totality and deadlock states.
"""


    //simple-indeterministic
    let checkValidInvariantStdout = """-- invariant (x = TRUE | x = FALSE)  is true
"""
    let checkValidInvariantStderr = """evaluating invariant (x = TRUE | x = FALSE) 
"""

    let checkValidCtlStdout = """-- specification AG (x = TRUE | x = FALSE)  is true
"""
    let checkValidCtlStderr = """evaluating specification AG (x = TRUE | x = FALSE)  
"""

    let checkValidLtlStdout = """-- specification  G (x = TRUE | x = FALSE)  is true
"""
    let checkValidLtlStderr = """evaluating LTL specification  G (x = TRUE | x = FALSE) 
Flattening the generated tableau........ done
Creating LTL tableau variables...

********   WARNING   ********
Fair states set of the finite state machine is empty.
This might make results of model checking not trustable.
******** END WARNING ********
"""
    
    //simple-indeterministic
    let checkInvalidInvariantStdout = """-- invariant x = TRUE  is false
-- as demonstrated by the following execution sequence
<?xml version="1.0" encoding="UTF-8"?>
<counter-example type="0" desc="AG alpha Counterexample" >
    <node>
        <state id="1">
            <value variable="x">TRUE</value>
        </state>
    </node>
    <node>
        <state id="2">
            <value variable="x">FALSE</value>
        </state>
    </node>
    <loops> </loops>
</counter-example>
"""
    let checkInvalidInvariantStderr = """evaluating invariant x = TRUE 
"""

    let checkInvalidCtlStdout = """-- specification AG x = TRUE  is false
-- as demonstrated by the following execution sequence
<?xml version="1.0" encoding="UTF-8"?>
<counter-example type="0" desc="CTL Counterexample" >
    <node>
        <state id="1">
            <value variable="x">TRUE</value>
        </state>
    </node>
    <node>
        <state id="2">
            <value variable="x">FALSE</value>
        </state>
    </node>
    <loops> </loops>
</counter-example>
"""
    let checkInvalidCtlStderr = """evaluating specification AG x = TRUE  
"""

    let checkInvalidLtlStdout = """-- specification  G x = TRUE  is false
-- as demonstrated by the following execution sequence
<?xml version="1.0" encoding="UTF-8"?>
<counter-example type="0" desc="LTL Counterexample" >
    <node>
        <state id="1">
            <value variable="x">TRUE</value>
        </state>
    </node>
    <node>
        <state id="2">
            <value variable="x">FALSE</value>
        </state>
    </node>
    <node>
        <state id="3">
            <value variable="x">TRUE</value>
        </state>
    </node>
    <loops> 1 </loops>
</counter-example>
"""
    let checkInvalidLtlStderr = """evaluating LTL specification  G x = TRUE 
Flattening the generated tableau........ done
Creating LTL tableau variables...
"""

    // simple-inputvariable
    // command: "check_ltlspec -p "G x=TRUE"
    let counterExampleWithInputXml = """<?xml version="1.0" encoding="UTF-8"?>
<counter-example type="0" desc="LTL Counterexample" >
        <node>
                <state id="1">
                        <value variable="x">TRUE</value>
                </state>
                <input id="2">
                        <value variable="i">FALSE</value>
                </input>
        </node>
        <node>
                <state id="2">
                        <value variable="x">FALSE</value>
                </state>
                <input id="3">
                        <value variable="i">FALSE</value>
                </input>
        </node>
        <node>
                <state id="3">
                        <value variable="x">TRUE</value>
                </state>
                <input id="4">
                        <value variable="i">TRUE</value>
                </input>
        </node>
        <node>
                <state id="4">
                        <value variable="x">TRUE</value>
                </state>
                <input id="5">
                        <value variable="i">TRUE</value>
                </input>
        </node>
        <node>
                <state id="5">
                        <value variable="x">TRUE</value>
                </state>
                <input id="6">
                        <value variable="i">TRUE</value>
                </input>
        </node>
        <node>
                <state id="6">
                        <value variable="x">TRUE</value>
                </state>
        </node>
        <loops> 1 ,3 ,4 ,5 </loops>
</counter-example>"""

    // simple-inputvariable
    // command: "check_ltlspec -p "G x=TRUE"
    let counterExampleWithInputSimple = """  -- Loop starts here
  -> State: 3.1 <-
    x = TRUE
  -> Input: 3.2 <-
    i = FALSE
  -> State: 3.2 <-
    x = FALSE
  -> Input: 3.3 <-
  -- Loop starts here
  -> State: 3.3 <-
    x = TRUE
  -> Input: 3.4 <-
    i = TRUE
  -- Loop starts here
  -> State: 3.4 <-
  -> Input: 3.5 <-
  -- Loop starts here
  -> State: 3.5 <-
  -> Input: 3.6 <-
  -> State: 3.6 <-"""
  

    // simple-combinatorial
    // command: "check_ltlspec -p "G x!=6"
    let counterExampleWithCombinatorialXml = """<?xml version="1.0" encoding="UTF-8"?>
<counter-example type="0" desc="LTL Counterexample" >
        <node>
                <state id="1">
                        <value variable="x">1</value>
                        <value variable="cx">1</value>
                </state>
                <combinatorial id="2">
                        <value variable="cix">2</value>
                </combinatorial>
                <input id="2">
                        <value variable="i">1</value>
                        <value variable="ci">1</value>
                </input>
        </node>
        <node>
                <state id="2">
                        <value variable="x">2</value>
                        <value variable="cx">2</value>
                </state>
                <combinatorial id="3">
                        <value variable="cix">4</value>
                </combinatorial>
                <input id="3">
                        <value variable="i">2</value>
                        <value variable="ci">2</value>
                </input>
        </node>
        <node>
                <state id="3">
                        <value variable="x">4</value>
                        <value variable="cx">4</value>
                </state>
                <combinatorial id="4">
                        <value variable="cix">6</value>
                </combinatorial>
                <input id="4">
                        <value variable="i">2</value>
                        <value variable="ci">2</value>
                </input>
        </node>
        <node>
                <state id="4">
                        <value variable="x">6</value>
                        <value variable="cx">6</value>
                </state>
                <combinatorial id="5">
                        <value variable="cix">7</value>
                </combinatorial>
                <input id="5">
                        <value variable="i">1</value>
                        <value variable="ci">1</value>
                </input>
        </node>
        <node>
                <state id="5">
                        <value variable="x">1</value>
                        <value variable="cx">1</value>
                </state>
                <combinatorial id="6">
                        <value variable="cix">2</value>
                </combinatorial>
                <input id="6">
                        <value variable="i">1</value>
                        <value variable="ci">1</value>
                </input>
        </node>
        <node>
                <state id="6">
                        <value variable="x">2</value>
                        <value variable="cx">2</value>
                </state>
                <combinatorial id="7">
                        <value variable="cix">2</value>
                </combinatorial>
                <input id="7">
                        <value variable="i">0</value>
                        <value variable="ci">0</value>
                </input>
        </node>
        <node>
                <state id="7">
                        <value variable="x">2</value>
                        <value variable="cx">2</value>
                </state>
        </node>
        <loops> 2 ,6 </loops>
</counter-example>"""


    [<Test>]
    let ``linesAsExpectedStr works correctly`` () =
        let testInput = "AAA\nABC\nADE"
        let expectationEmpty = []
        let expectationTrue1 = ["A";"AB";"AD"]
        let expectationFalse1 = ["A";"AB";"AE"]
        let expectationFalse2 = ["D";"AB";"AD"]
        let expectationFalse3 = ["A";"AB";"AD";"E"]
        NuXmvInterpretResult.linesAsExpectedStr testInput expectationEmpty =? true
        NuXmvInterpretResult.linesAsExpectedStr testInput expectationTrue1 =? true
        NuXmvInterpretResult.linesAsExpectedStr testInput expectationFalse1 =? false
        NuXmvInterpretResult.linesAsExpectedStr testInput expectationFalse2 =? false
        NuXmvInterpretResult.linesAsExpectedStr testInput expectationFalse2 =? false
        

    [<Test>]
    let ``interpret failed flatten_command correctly`` () =
        let commandResult= {
            NuXmvCommandResultBasic.Command = NuSMVCommand.FlattenHierarchy;
            NuXmvCommandResultBasic.Stderr  = ``flatten_hierarchy-ResultStderrFailed``;
            NuXmvCommandResultBasic.Stdout  = ``flatten_hierarchy-ResultStdoutFailed``;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let interpretedResult = NuXmvInterpretResult.interpretResult commandResult
        interpretedResult.HasSucceeded =? false
        
    [<Test>]
    let ``interpret successful flatten_command correctly`` () =
        let commandResult= {
            NuXmvCommandResultBasic.Command = NuSMVCommand.FlattenHierarchy;
            NuXmvCommandResultBasic.Stderr  = ``flatten_hierarchy-ResultStderrSuccess``;
            NuXmvCommandResultBasic.Stdout  = ``flatten_hierarchy-ResultStdoutSuccess``;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let interpretedResult = NuXmvInterpretResult.interpretResult commandResult
        interpretedResult.HasSucceeded =? true
                           
    [<Test>]
    let ``interpret result of check_fsm correctly`` () =
        let dummyExpression = SimpleExpression.ConstExpression(ConstExpression.BooleanConstant(true))
        let commandResultCheckFsmNotTotalWithDeadlock = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckFsm;
            NuXmvCommandResultBasic.Stderr  = checkFsmNotTotalWithDeadlockStderr;
            NuXmvCommandResultBasic.Stdout  = checkFsmNotTotalWithDeadlockStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let commandResultCheckFsmNotTotalWithoutDeadlock = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckFsm;
            NuXmvCommandResultBasic.Stderr  = checkFsmNotTotalWithoutDeadlockStderr;
            NuXmvCommandResultBasic.Stdout  = checkFsmNotTotalWithoutDeadlockStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let commandResultCheckFsmTotal = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckFsm;
            NuXmvCommandResultBasic.Stderr  = checkFsmTotalStderr;
            NuXmvCommandResultBasic.Stdout  = checkFsmTotalStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let interpretedResultNotTotalWithDeadlock = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm commandResultCheckFsmNotTotalWithDeadlock
        let interpretedResultNotTotalWithoutDeadlock = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm commandResultCheckFsmNotTotalWithoutDeadlock
        let interpretedResultTotal = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckFsm commandResultCheckFsmTotal
        interpretedResultNotTotalWithDeadlock.IsTotal =? false
        interpretedResultNotTotalWithDeadlock.IsDeadlockFree =? false
        interpretedResultNotTotalWithoutDeadlock.IsTotal =? false
        interpretedResultNotTotalWithoutDeadlock.IsDeadlockFree =? true
        interpretedResultTotal.IsTotal =? true
        interpretedResultTotal.IsDeadlockFree =? true
                                
    [<Test>]
    let ``interpret successful verifications correctly`` () =
        let dummyExpression = SimpleExpression.ConstExpression(ConstExpression.BooleanConstant(true))
        let commandResultCheckInvar = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckInvar(dummyExpression);
            NuXmvCommandResultBasic.Stderr  = checkValidInvariantStderr;
            NuXmvCommandResultBasic.Stdout  = checkValidInvariantStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let commandResultCheckCtl = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckCtlSpec(CtlExpression.CtlSimpleExpression(dummyExpression));
            NuXmvCommandResultBasic.Stderr  = checkValidCtlStderr;
            NuXmvCommandResultBasic.Stdout  = checkValidCtlStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let commandResultCheckLtl = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckLtlSpec(LtlExpression.LtlSimpleExpression(dummyExpression));
            NuXmvCommandResultBasic.Stderr  = checkValidLtlStderr;
            NuXmvCommandResultBasic.Stdout  = checkValidLtlStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let interpretedResultInvar = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar commandResultCheckInvar
        let interpretedResultCtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec commandResultCheckCtl
        let interpretedResultLtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec commandResultCheckLtl
        interpretedResultInvar.Result.IsSpecValid =? true
        interpretedResultCtl.Result.IsSpecValid =? true
        interpretedResultLtl.Result.IsSpecValid =? true

    [<Test>]
    let ``interpret verification result with counterexample correctly`` () =
        let dummyExpression = SimpleExpression.ConstExpression(ConstExpression.BooleanConstant(true))
        let commandResultCheckInvar = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckInvar(dummyExpression);
            NuXmvCommandResultBasic.Stderr  = checkInvalidInvariantStderr;
            NuXmvCommandResultBasic.Stdout  = checkInvalidInvariantStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let commandResultCheckCtl = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckCtlSpec(CtlExpression.CtlSimpleExpression(dummyExpression));
            NuXmvCommandResultBasic.Stderr  = checkInvalidCtlStderr;
            NuXmvCommandResultBasic.Stdout  = checkInvalidCtlStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let commandResultCheckLtl = {
            NuXmvCommandResultBasic.Command = NuSMVCommand.CheckLtlSpec(LtlExpression.LtlSimpleExpression(dummyExpression));
            NuXmvCommandResultBasic.Stderr  = checkInvalidLtlStderr;
            NuXmvCommandResultBasic.Stdout  = checkInvalidLtlStdout;
            NuXmvCommandResultBasic.Failure = Some(CommandResultProcessingFailure.Unclear);
        }
        let interpretedResultInvar = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckInvar commandResultCheckInvar
        let interpretedResultCtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckCtlSpec commandResultCheckCtl
        let interpretedResultLtl = NuXmvInterpretResult.interpretResultOfNuSMVCommandCheckLtlSpec commandResultCheckLtl
        interpretedResultInvar.Result.IsSpecValid =? false
        match interpretedResultInvar.Result with
            | CheckOfSpecificationDetailedResult.Invalid(Some(counterexample)) ->
                counterexample.Loops =? [] // check_invar does not return loops
                counterexample.NumberOfLastExplicitStep =? 2
            | _ -> failwith "formula should be invalid and contain a counterexample"
        interpretedResultCtl.Result.IsSpecValid =? false
        match interpretedResultCtl.Result with
            | CheckOfSpecificationDetailedResult.Invalid(Some(counterexample)) ->
                counterexample.Loops =? []
                counterexample.NumberOfLastExplicitStep =? 2
            | _ -> failwith "formula should be invalid and contain a counterexample"
        interpretedResultLtl.Result.IsSpecValid =? false
        match interpretedResultLtl.Result with
            | CheckOfSpecificationDetailedResult.Invalid(Some(counterexample)) ->
                counterexample.Loops =? [1]
                counterexample.NumberOfLastExplicitStep =? 3
            | _ -> failwith "formula should be invalid and contain a counterexample"
    
    [<Test>]
    let ``interpret xml counterexample with combinatorial correctly`` () =
        let interpretedResult = NuXmvInterpretResult.interpretCounterExample counterExampleWithCombinatorialXml
        interpretedResult.Loops =? [2; 6]
        interpretedResult.NumberOfLastExplicitStep =? 7
        ()

    [<Test>]
    let ``interpret xml counterexample with input variable correctly`` () =
        let interpretedResult = NuXmvInterpretResult.interpretCounterExample counterExampleWithInputXml
        interpretedResult.Loops =? [1; 3; 4; 5]
        interpretedResult.NumberOfLastExplicitStep =? 6
        ()