// Generate TeX output of Tsam-Stuff
// I) Different forms of Sourcecode
//    A. Sourcefile
//       text, graph
//    B. remove nested blocks
//       text, graph
//    C. Treeified
//       text, graph
//    D. Single Static Assignment
//       text, graph
//    E. Passive Form
//       text, graph
//    F. Gwa Form (My Form)
//       text, graph, transformations in between
//  II) Different Transformations to merge statements to a big step
//    1. Weakest Precondition (from E)
//        * show problem, why it does not work in the indeterministic case
//    2. Strongest Postcondition (from E)
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







[<EntryPoint>]
let main argv = 
    printfn "%A" argv
    0 // return an integer exit code
