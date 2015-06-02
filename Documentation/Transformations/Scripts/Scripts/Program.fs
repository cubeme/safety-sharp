﻿// Generate TeX output of Tsam-Stuff
//  I) Different forms of source code
//    A. Source file
//       text, graph
//    B. Single Static Assignment (GCFK09-Algorithm)
//       text, graph
//    C. Passive Form (GCFK09-Algorithm)
//       text, graph
//    D. remove nested blocks
//       text, graph
//    E. Treeified
//       text, graph. Show problem of large expressions
//    F. Gwa Form (My Form)
//       text, graph, transformations in between
//  II) Different Transformations to merge statements to a big step
//    1. Weakest Precondition (from C)
//        * show problem, why it does not work in the indeterministic case
//    2. Strongest Postcondition (from C)
//        * show problem with instantiation of exists quantifier
//        * show that input variables are necessary
//    3. Gwa-Form (From F) with Strongest Postcondition
//        * show problem of resulting large expressions
//  III) Different model checker inputs
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

// TODO: Maybe make real reports out of it

namespace SafetySharp.Documentation.Scripts

module TsamToTex =

    open SafetySharp.Models.Tsam
    open SafetySharp.Models.TsamMutable
    open SafetySharp.Workflow

    type OutputStyleDecorator = {
        Content : string->string;
        Section : string->string;
        TsamSource : string->string;
        Graph : string->string;
    }
        
    let generateFile (outputstyle:OutputStyleDecorator) (useOnlyTransformationsWithStochasticSupport:bool) (path:string) (filename:string) : string =
        let tsamSourceModel =
            let readInputFileAndGenerateDotFile = workflow {
                    do! readFile filename
                    do! SafetySharp.Models.SamParser.parseStringWorkflow
                    do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
            }
            runWorkflow_getState readInputFileAndGenerateDotFile
            
        let output_I_complete : string =
            let printModelAsTextAndGraphWorkflow (chapter:string) = workflow {
                    let! modelToPrint = getState ()
                    do! SafetySharp.Models.TsamToString.exportModelWorkflow ()
                    let! modelAsText = getState ()
                    do! updateState modelToPrint
                    do! SafetySharp.Models.TsamToDot.exportModelWorkflow ()
                    do! SafetySharp.GraphVizDot.DotToString.exportDotPlainFile ()
                    let! modelAsGraph = getState ()
                    return (outputstyle.Section chapter) + (outputstyle.TsamSource modelAsText) + (outputstyle.Graph modelAsGraph)
            }
                       
            let output_I_A_wf () = workflow {
                do! updateState tsamSourceModel
                let! result = printModelAsTextAndGraphWorkflow ("Original Model")
                return result
            }
            let output_I_B_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                let! result = printModelAsTextAndGraphWorkflow ("Single Static Assignment (GCFK09-Algorithm)")
                return result
            }
            let output_I_C_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
                let! result = printModelAsTextAndGraphWorkflow ("Passive Form (GCFK09-Algorithm)")
                return result
            }
            let output_I_D_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamMutable.unnestBlocks ()
                let! result = printModelAsTextAndGraphWorkflow ("remove nested blocks")
                return result
            }
            let output_I_E_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamMutable.treeifyStm ()
                let! result = printModelAsTextAndGraphWorkflow ("Treeified")
                return result
            }
            let output_I_F_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToTsamInGuardToAssignmentForm ()
                let! result = printModelAsTextAndGraphWorkflow ("Gwa Form (My Form)")
                return result
            }
                            
            let outputWorkflow = workflow {
                let! output_I_A = output_I_A_wf ()
                let! output_I_B = output_I_B_wf ()
                let! output_I_C = output_I_C_wf ()
                let! output_I_D = output_I_D_wf ()
                let! output_I_E = output_I_E_wf ()
                let! output_I_F = output_I_F_wf ()
                return output_I_A + output_I_B + output_I_C + output_I_D + output_I_E + output_I_F
            }
            runWorkflow_getResult outputWorkflow
                    
        let completeOutput : string =
            let content = sprintf "%s" output_I_complete
            outputstyle.Content content
        do SafetySharp.FileSystem.WriteToAsciiFile path completeOutput
        completeOutput

        
    let texOutput : OutputStyleDecorator =
        let contentDecoration (content:string) = 
            let texTemplateAsString = """
\documentclass[a4paper, 12pt,titlepage]{scrartcl}
%s
%s
\begin{document}
%s
\end{document}
"""
            let texTemplate = Printf.StringFormat<_,string>(texTemplateAsString)
            sprintf texTemplate (SafetySharp.GraphVizDot.DotToString.texFilePackagesInHeader) (SafetySharp.Models.TsamToString.texFilePackagesInHeader) content        
        let sectionDecoration (chapterName:string) = sprintf "\\section{%s}\n" chapterName
        let tsamSourceDecorator (tsamSource:string) = sprintf "\n{\\scriptsize\n\\begin{lstlisting}\n%s\n\\end{lstlisting}\n}\n" tsamSource
        let graphDecorator (graph:string) = sprintf "\n\\begin{tikzpicture}[>=latex',scale=0.5]\n\\begin{dot2tex}[dot,tikz,options=-s -tmath]\n%s\\end{dot2tex}.\n\\end{tikzpicture}\n" graph
        {
            OutputStyleDecorator.Content = contentDecoration
            OutputStyleDecorator.Section = sectionDecoration;
            OutputStyleDecorator.TsamSource = tsamSourceDecorator;
            OutputStyleDecorator.Graph = graphDecorator;
        }

    let generateTexFile = generateFile texOutput
        (*
        let generateIII (filename:string) : string =
            // III 1:
            let promelaSmokeTestWorkflow (inputFile:string) = workflow {    
                    do! readFile inputFile
                    do! SafetySharp.Models.SamParser.parseStringWorkflow
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf ()
                    do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                    do! SafetySharp.ITracing.removeTracing ()
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                    let filename = sprintf "%s.pml" (System.IO.Path.GetFileName(inputFile) ) |> SafetySharp.FileSystem.FileName
                    do! saveToFile filename
                    do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPan ()
            }
            // III 2:     
            // III 3:   
            let nuxmv2smokeTestWorkflow (inputFile:string) = workflow {
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModelFast.transformWorkflow ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformGwamToTsareWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.NuXmvToString.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }
            // III 4:
            // III 5:
            // III 6:
            let prismSmokeTestWorkflow (inputFile:string) = workflow {
                do! readFile inputFile
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModelFast.transformWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.Prism.GwamToPrism.transformWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.Prism.ExportPrismAstToFile.workflow ()
                let outputFile = inputFileNameToOutputFileName inputFile
                do! printToFile outputFile
            }

            //let runSmokeTest (inputFile) =
            //    SafetySharp.Workflow.runWorkflow_getState (smokeTestWorkflow inputFile)
            *)

open NUnit.Framework

[<TestFixture>]
module TsamToTexTest =
    open SafetySharp.Workflow
    
    // NOTE: Make sure, we use the same F#-version as the SafetySharp Project. Otherwise it cannot be started. See App.config for details
    
    [<Test>]
    let testWithSmokeTest8 () =        
        let useOnlyStochastic = false
        let path = "../../"

        let output = TsamToTex.generateTexFile useOnlyStochastic (path+"/smokeTest8.tex") (path + "/../../../../Examples/SAM/smokeTest8.sam")
        printfn "%s" output
        ()

    [<Test>]
    let testWithSmokeTest9 () =        
        let useOnlyStochastic = false
        let path = "../../"

        let output = TsamToTex.generateTexFile useOnlyStochastic (path+"/smokeTest9.tex") (path + "/../../../../Examples/SAM/smokeTest9.sam")
        printfn "%s" output
        ()

    [<Test>]
    let testWithSmokeTest10 () =        
        let useOnlyStochastic = false
        let path = "../../"

        let output = TsamToTex.generateTexFile useOnlyStochastic (path+"/smokeTest10.tex") (path + "/../../../../Examples/SAM/smokeTest10.sam")
        printfn "%s" output
        ()