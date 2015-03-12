## Casual Tests

* simpleArithmetical1.sam: example
* simpleArithmetical2.sam: example
* simpleBoolean1.sam: example
* simpleGuardedCommands1.sam: example
* simpleGuardedCommands2.sam: example
* simpleGuardedCommands3.sam: example
* simpleGuardedCommands4.sam: example
* simplePrev.sam: example


## Smoke Tests of evaluation

* smokeTest1.sam: example, which should return 200 (http for OK)
* smokeTest15.sam: example, which has one branch, which always works, and one branch, which stops (in VcSam equivalent: "assume false" anywhere). Promela just stops the execution in such a branch. Check, if model checking of formulas is still valid.