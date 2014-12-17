## parsing Tests

* nestedComponent1.scm: 2 Components with do-nothing behaviour: 1 parent with 1 subcomponent.
* nestedComponent2.scm: 5 Components with do-nothing behaviour: 1 parent with 2 subcomponents. Each subcomponent has 1 subcomponent
* simpleComponent1.scm: 1 Component with do-nothing behaviour
* simpleComponent2.scm: 1 Component with do-nothing behaviour and 5 fields with indeterministic initialization. Use "krun simpleComponent2.scm --search-final" to get all results
* simpleComponent3.scm: 1 Component with do-nothing behaviour and 2 fields with the same name (incorrect program)
* simpleComponent4.scm: 1 Component with do-nothing behaviour and 1 required port
* simpleComponent5.scm: 1 Component with do-nothing behaviour and 1 provided port
* simpleComponent6.scm: 1 Component with do-nothing behaviour and 1 provided port, 2 required ports, 1 instantaneous binding, 1 delayed binding
* undeclaredIdentifier1.scm: Assignment to a inout, which is out of scope, because it was declared in a previous provided port (incorrect program)
* undeclaredIdentifier2.scm: Assignment to a inout, which is out of scope, because it was declared in a previous required port (incorrect program)
* undeclaredIdentifier3.scm: Assignment to a inout, which is out of scope, because it was declared in a port of a nested component (incorrect program)
* undeclaredIdentifier4.scm: Assignment to a field in a nested class, which is out of scope (incorrect program)


## simple Statements Tests

(everything except (beh) and (call))

* simpleStatement1.scm: 1 Component with one local variable, assignment to variable
* simpleStatement2.scm: 1 Component with one field, assignment to field with current field value
* simpleStatement3.scm: 1 Component with one local variable, assignment to local variable, reading from local variable


## (cmd)-Tests

* cmd1.scm: 1 Component with one guardedCommand, which makes an indeterministic field assignment. Use "krun cmd1.scm --search-final" to get all results


## (beh)-Tests

* beh1.scm: 2 Components. 1 parent with 1 subcomponent. Parent calls behaviour of its subcomponent
* beh2.scm: Like beh1. Additionally  the behaviours of both components make field assignments
* beh3.scm: Like beh2. Additionally  the behaviours of both components make local variable assignments
* beh4.scm: Like beh3. But stops during the execution (for better introspection)


## (call)-Tests (instantaneous)

* callInstFromBeh1.scm: just call from behaviour a requiredPort inside the same Component
* callInstFromBeh2.scm: call from _behaviour_ a requiredPort which calls a required Port inside the same Component
* callInstFromBeh3.scm: like callInst1, but with field assignments
* callInstFromBeh4.scm: like callInst3, but with input-parameters
* callInstFromBeh5.scm: like callInst1, but with an inout-parameter, which was preassigned (field) and gets a value (incorrect program)
* callInstFromBeh6.scm: like callInst1, but with an inout-parameter, which was preassigned (local) and gets a value
* callInstFromBeh7.scm: like callInst1, but with an inout-parameter, which was not preassigned and gets no value
* callInstFromBeh8.scm: like callInst1, but with an inout-parameter, which was not preassigned and gets a value
* callInstFromProv1.scm: tests, if inout- reading/writing works with Required Ports, if called within an provided port
* callInstHierarchy1.scm: tests hierarchical case: RequiredPortComponent = ProvidedPortComponent. Binding declared in this component
* callInstHierarchy2.scm: tests hierarchical case: RequiredPortComponent = ProvidedPortComponent. Binding declared in its parent component.
* callInstHierarchy3.scm: tests hierarchical case: parent(RequiredPortComponent) = ProvidedPortComponent). Binding declared in ProvidedPortComponent
* callInstHierarchy4.scm: tests hierarchical case: RequiredPortComponent = parent(ProvidedPortComponent). Binding declared in RequiredPortComponent
* callInstHierarchy5.scm: tests hierarchical case: parent(RequiredPortComponent) = parent(ProvidedPortComponent; RequiredPortComponent!=ProvidedPortComponent). Binding declared in common parent


## (call)-Tests (delayed)



## Examples which combine several aspects

* exampleDocumentationFull.scm: Test from the semantics-pdf
* exampleDocumentationSimplified1.scm: like exampleDocumentationFull, but with faults
* exampleDocumentationSimplified2.scm: like exampleDocumentationSimplified1, but with instantaneous binding instead of delayed
* exampleBackupRecovery1.scm: Source [1,2]. Only use inouts, avoid behaviours
* exampleBackupRecovery2.scm: Like exampleBackupRecovery1, but extract function "doValuesMatchP" into an extra port (to have a case, where we can use input parameters). Combine "deactivate" and "activate" into a common port with input parameter
* exampleBackupRecovery3.scm: Like exampleBackupRecovery1, but do the major work in the behaviours of every component. Use ports just for value transmitting. Save output values of every component in its fields. Ports are only called in behaviours. Order of behaviour-call matters. 




##Literature of Case Studies

* [1] Martin Walker, Leonardo Bottaci, and Yiannis Papadopoulos. Compositional Temporal Fault Tree Analysis. SAFECOMP 2007, LNCS 4680, pp. 106–119, 2007. Springer-Verlag Berlin Heidelberg.
* [2] Matthias Güdemann. Qualitative and Quantitative Formal Model-Based Safety Analysis.