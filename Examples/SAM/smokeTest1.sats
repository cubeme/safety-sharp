do setEmptyMainModel "simple";
do injectSamModel "../../Examples/SAM/smokeTest1.sam" "simple";
//let check1 = verifyLtl "X (simple.i == 200)";
let check2 = verifyLtl "G (simple.i == 200)";
//let check3 = verifyLtl "X (G (simple.i == 200))";
//let check4 = verifyLtl "X (simple.i == 0)";
let check5 = verifyLtl "G ((simple.i == 200)||(simple.i == 0))";
//expect check1.result = valid;
expect check2.result = invalid;
//expect check3.result = valid;
//expect check4.result = invalid;
expect check5.result = valid;
