## Casual Tests

* simpleArithmetical1.sam: example
* simpleArithmetical2.sam: example
* simpleBoolean1.sam: example
* simpleGuardedCommands1.sam: example
* simpleGuardedCommands2.sam: example
* simpleGuardedCommands3.sam: example
* simpleGuardedCommands4.sam: example
* simplePrev.sam: example
* reservedNames.sam: Example, which contains all reserved Names of Prism. TODO: Other model checkers
* overflowIntError1.sam: Upper bound
* overflowIntError2.sam: Lower bound
* overflowIntWrapAround1.sam: Upper bound 
* overflowIntWrapAround2.sam: Upper bound twice the range
* overflowIntWrapAround3.sam: Lower bound 
* overflowIntWrapAround4.sam: Lower bound twice the range
* overflowIntClamp1.sam: upper bound
* overflowIntClamp2.sam: lower bound

## Smoke Tests of evaluation

* smokeTest1.sam: example, which should return 200 (http for OK)
* smokeTest6.sam: example to check: Must not be true: (next(i)=1 & next(j)=2). Must be true (next(i)=1 | next(j)=2)
* smokeTest17.sam: example, which has one branch, which always works, and one branch, which stops (in VcSam equivalent: "assume false" anywhere). Promela just stops the execution in such a branch. Check, if model checking of formulas is still valid.
* smokeTest18.sam: like 4, but start with an assumption
* smokeTest19.sam: one branch allows a value, another does not
* smokeTest20.sam: example, which demonstrates, that the definition of assignment in the sp predicate transformer actually needs an \exists