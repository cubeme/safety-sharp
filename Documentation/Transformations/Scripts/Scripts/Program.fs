// Generate TeX output of Tsam-Stuff
// I) Different forms of Sourcecode
//    A. Sourcefile
//       text, graph
//    B. Single Static Assignment
//       text, graph
//    C. Passive Form
//       text, graph
//    D. remove nested blocks
//       text, graph
//    E. Treeified
//       text, graph
//    F. Gwa Form (My Form)
//       text, graph, transformations in between
//  II) Different Transformations to merge statements to a big step
//    1. Weakest Precondition (from C)
//        * show problem, why it does not work in the indeterministic case
//    2. Strongest Postcondition (from C)
//        * show problem with instantiation of exists quantifier
//        * show that input variables are necessary
//    3. Gwa-Form (From F)
//        * show problem 
// III) Different model checker inputs
//    1. Promela/Spin (direct) from I A
//    2. NuXmv/NuSMV from I A
//    3. NuXmv/NuSMV from II 2
//    4. NuXmv/NuSMV from II 3
//    5. Prism from  I A
//    6. Prism from  II 3


// Generate TeX output of Scm-Stuff
// 1. Upleveling of Subcomponents
// 2. Conversion of Faults
// 3. Conversion of Delayed Ports
// 4. Inlining of Ports





[<EntryPoint>]
let main argv = 
    printfn "%A" argv
    0 // return an integer exit code
