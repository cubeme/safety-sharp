do setEmptyModel
do injectSamModel "simple" "smokeTest1.sam";
let check1 = verifyLtl "X (i == 200)";
let check2 = verifyLtl "G (i == 200)";
let check3 = verifyLtl "X (G (i == 200))";
let check4 = verifyLtl "X (i == 0)";
expect check1.result = valid;
expect check2.result = invalid;
expect check3.result = valid;
expect check4.result = invalid;
