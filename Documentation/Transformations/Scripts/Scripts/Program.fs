// Generate TeX output of Tsam-Stuff
//  I) Different forms of source code
//    A. Source file
//       text, graph
//    B. Single Static Assignment (GCFK09-Algorithm)
//       text, graph
//       * also introduces for every global variable which has never written to a new assignment "v := v" to keep its value
//    C. Passive Form (GCFK09-Algorithm)
//       text, graph
//    D. remove nested blocks
//       text, graph
//    E. Treeified
//       text, graph. Show problem of large expressions
//    F. Gwa Form (My Form)
//       text, graph, transformations in between
//  II) Different Transformations to merge statements to a big step
//    1. Transition system <--Weakest Precondition-- IA
//        * show problem, why it does not work in the indeterministic case
//    2. Transition system <--Weakest Precondition-- IC (Passive Form) <---- IA
//        * show problem, why it does not work in the indeterministic case
//        * show that using (from C) reduces the size of the condition, but adds new input variables
//    3. Transition system <--Strongest Postcondition-- IC (Passive Form) <---- IA
//        * show that input variables are necessary.
//          show problem with instantiation of exists quantifier (if we try from A)
//    4. Transition system <--Strongest Postcondition (optimized)-- IC (Passive Form) <---- IA
//        * show that input variables are necessary.
//          show problem with instantiation of exists quantifier (if we try from A)
//        * The way presented here is optimized: It reduces the number of input variables in lots of cases.
//    5. Transition system <--Propagation--  IE (Tree Form) <--treeify-- SSA Form (IB) <---- IA
//        * SSA-Form necessary. Otherwise building formula is difficult, because we may only "write down"
//          a variable the _last_ time it was written to
//        * similar to Strongest Postcondition.  Propagation of variable substitution (merging of last statements)
//        * show problem of resulting large expressions
//        * show that it only works for systems, where transition relation can be entered directly
//    6. Transition system <--...-- Gwa-Model  <--Gwa-Propagation-- IF(Gwa-Form) <---- IA
//        * propagation here is mainly the merging of the last statements
//        * currently only way to transform to prism and remove local variables
//        * Transformation from Gwa-Form to Gwa model also ensures that _every_ variable (even those not written to at all)
//          has an assignment. Transformation to Gwa-Form does not assure that
//        * show problem of resulting large expressions
//        * show also Gwa-Model as step in between
//        * show transformation of Gwa-Model to Transition system to demonstrate the semantics of the Gwa-Model as classical transition system.
//          If a TS is needed without local variables II 5 seems superior.
//    7. Transition system <--Propagation-- IF(Gwa-Form) <--treeify-- SSA Form (IB) <---- IA
//        * propagation here is done directly with algorithm of II 5
//        * This transformation is only to compare this result with II 6 and II 5.
//          If a TS is needed without local variables II 5 seems superior.
//  III) Different model checker languages
//    1. Promela/Spin (direct) from I A
//          (Problem of getting stuck, if assertion invalid, how is it handled)
//    2. NuXmv/NuSMV from I A
//          (Problem of getting stuck, if assertion invalid, how is it handled)
//    3. NuXmv/NuSMV from II 4
//    4. NuXmv/NuSMV from II 5
//    5. NuXmv/NuSMV from II 6
//    6. Prism from  I A (same limitations apply to SAML)
//    7. Prism from Gwa-Model (of II 6) (same limitations apply to SAML)


// Generate TeX output of Scm-Stuff
// 1. Upleveling of Subcomponents
// 2. Conversion of Faults
// 3. Conversion of Delayed Ports
// 4. Inlining of Ports

// TODO: Maybe make real reports out of it


namespace SafetySharp.Documentation.Scripts

module TsamToReport =

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

        let output_II_complete : string =

            let output_II_1_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithWpWorkflow true
                let! model = getState ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! modelAsText = getState ()
                let formulaTrueAtTheEnd =
                    // See TransitionSystemAsRelationExpr TODO: Find a better way that actually uses the real code
                    let postConditionAsFormula =
                        let createFormulaForGlobalVarDecl (globalVar:SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.VarDecl) =
                            let primedVar = match globalVar.Var with | Var.Var (name) -> name + "'"
                            Expr.BExpr(Expr.Read(Var.Var(primedVar)),BOp.Equals,Expr.Read(globalVar.Var))
                        model.TransitionSystem.Globals
                            |> List.map createFormulaForGlobalVarDecl
                            |> SafetySharp.Models.TsamHelpers.createAndedExpr
                    let exprAsString = SafetySharp.Models.TsamToString.exportExpr postConditionAsFormula SafetySharp.Models.SamToStringHelpers.AstToStringState.initial
                    exprAsString.ToString()
                let result = sprintf "Formula, which expresses the states at the end (precondition):%s\n\n%s" formulaTrueAtTheEnd modelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--Weakest Precondition-- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }
                       
            let output_II_2_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithWpWorkflow true
                let! model = getState ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! modelAsText = getState ()
                let formulaTrueAtTheEnd =
                    // See TransitionSystemAsRelationExpr TODO: Find a better way that actually uses the real code
                    let postConditionAsFormula =
                        let createFormulaForGlobalVarDecl (globalVar:SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.VarDecl) =
                            let primedVar = match globalVar.Var with | Var.Var (name) -> name + "'"
                            Expr.BExpr(Expr.Read(Var.Var(primedVar)),BOp.Equals,Expr.Read(globalVar.Var))
                        model.TransitionSystem.Globals
                            |> List.map createFormulaForGlobalVarDecl
                            |> SafetySharp.Models.TsamHelpers.createAndedExpr
                    let exprAsString = SafetySharp.Models.TsamToString.exportExpr postConditionAsFormula SafetySharp.Models.SamToStringHelpers.AstToStringState.initial
                    exprAsString.ToString()
                let result = sprintf "Formula, which expresses the states at the end (precondition):%s\n\n%s" formulaTrueAtTheEnd modelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--Weakest Precondition-- IC (Passive Form) <---- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }
                       
            let output_II_3_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithSpUnoptimizedWorkflow ()
                let! model = getState ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! modelAsText = getState ()
                let formulaTrueInTheBeginning = "true" //hardcoded
                let formulaToAddAtTheEnd =
                    // See TransitionSystemAsRelationExpr TODO: Find a better way that actually uses the real code
                    let globalNextExpr =
                        let createEntry (globalVar:SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.VarDecl) =
                            let primedVar = match globalVar.Var with | Var.Var (name) -> name + "'"
                            Expr.BExpr(Expr.Read(Var.Var(primedVar)),BOp.Equals,Expr.Read(model.TransitionSystem.VarToVirtualNextVar.Item globalVar.Var))
                        model.TransitionSystem.Globals
                            |> List.map createEntry
                            |> SafetySharp.Models.TsamHelpers.createAndedExpr
                    let exprAsString = SafetySharp.Models.TsamToString.exportExpr globalNextExpr SafetySharp.Models.SamToStringHelpers.AstToStringState.initial
                    exprAsString.ToString()
                let result = sprintf "Formula, which expresses the state(s) in the beginning (precondition):%s\nExpression to add to sp(Pgm,precondition):%s\n%s" formulaTrueInTheBeginning formulaToAddAtTheEnd modelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--Strongest Postcondition-- IC (Passive Form) <---- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }

            let output_II_4_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithSpWorkflow ()
                let! model = getState ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! modelAsText = getState ()
                let formulaTrueInTheBeginning = "true" //hardcoded
                let formulaToAddAtTheEnd =
                    // The transformation algorithm actually uses an optimization: If a virtual variable version was created, the last one is used as next variable.
                    // If none was created, we must add next(var)=var by hand. See TransitionSystemAsRelationExpr TODO: Find a better way that actually uses the real code
                    ""
                let result = sprintf "Formula, which expresses the state(s) in the beginning (precondition):%s\n%s" formulaTrueInTheBeginning modelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--Strongest Postcondition (optimized)-- IC (Passive Form) <---- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }

            let output_II_5_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Models.TsamMutable.treeifyStm ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithPropagationWorkflow ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! tsModelAsText = getState ()
                let result = tsModelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--Propagation--  IE (Tree Form) <--treeify-- SSA Form (IB) <---- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }
                       
            let output_II_6_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow ()
                let! gwamModel = getState ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.modelToStringWorkflow ()
                let! gwamModelAsText = getState ()
                do! updateState gwamModel
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformGwamToTsareWorkflow ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! tsModelAsText = getState ()
                let result = sprintf "Guard With Assignment Model:\n%s\n%s" gwamModelAsText tsModelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--...-- Gwa-Model  <--Gwa-Propagation-- IF(Gwa-Form) <---- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }
                       
            let output_II_7_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToTsamInGuardToAssignmentForm()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithPropagationWorkflow ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.modelToStringWorkflow ()
                let! tsModelAsText = getState ()
                let result = tsModelAsText
                let resultDecorated = (outputstyle.Section "Transition system <--Propagation-- IF(Gwa-Form) <--treeify-- SSA Form (IB) <---- IA") + (outputstyle.TsamSource result)
                return resultDecorated
            }
                            
            let outputWorkflow = workflow {
                let! output_II_1 = output_II_1_wf ()
                let! output_II_2 = output_II_2_wf ()
                let! output_II_3 = output_II_3_wf ()
                let! output_II_4 = output_II_4_wf ()
                let! output_II_5 = output_II_5_wf ()
                let! output_II_6 = output_II_6_wf ()
                let! output_II_7 = output_II_7_wf ()
                return output_II_1 + output_II_2 + output_II_3 + output_II_4 + output_II_5 + output_II_6 + output_II_7
            }
            runWorkflow_getResult outputWorkflow

            
        let output_III_complete : string =
        
            let output_III_1_wf () = workflow {
                do! readFile filename
                do! SafetySharp.Models.SamParser.parseStringWorkflow
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow ()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "Promela/Spin (direct) from I A") + (outputstyle.TsamSource result)
                return resultDecorated
            }
        
            let output_III_2_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamToSpg.transformToStochasticProgramGraphWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.StochasticProgramGraphToNuXmv.transformProgramGraphToNuXmvWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.NuXmvToString.workflow()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "NuXmv/NuSMV from I A") + (outputstyle.TsamSource result)
                return resultDecorated
            }
            
            let output_III_3_wf () = workflow {
                //II 4. Transition system <--Strongest Postcondition (optimized)-- IC (Passive Form) <---- IA
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithSpWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.NuXmvToString.workflow ()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "NuXmv/NuSMV from II 4") + (outputstyle.TsamSource result)
                return resultDecorated
            }
            let output_III_4_wf () = workflow {
                //II 5. Transition system <--Propagation--  IE (Tree Form) <--treeify-- SSA Form (IB) <---- IA
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
                do! SafetySharp.Models.TsamMutable.treeifyStm ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithPropagationWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.NuXmvToString.workflow ()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "NuXmv/NuSMV from II 5") + (outputstyle.TsamSource result)
                return resultDecorated
            }
            let output_III_5_wf () = workflow {
                //II 6. Transition system <--...-- Gwa-Model  <--Gwa-Propagation-- IF(Gwa-Form) <---- IA
                do! updateState tsamSourceModel
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow ()
                do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformGwamToTsareWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.NuXmv.NuXmvToString.workflow ()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "NuXmv/NuSMV from II 6") + (outputstyle.TsamSource result)
                return resultDecorated
            }
            let output_III_6_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Models.TsamToSpg.transformToStochasticProgramGraphWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.Prism.StochasticProgramGraphToPrism.transformWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.Prism.ExportPrismAstToFile.workflow ()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "Prism from  I A") + (outputstyle.TsamSource result)
                return resultDecorated
            }
            let output_III_7_wf () = workflow {
                do! updateState tsamSourceModel
                do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow ()
                do! SafetySharp.Analysis.Modelchecking.Prism.GwamToPrism.transformWorkflow ()
                do! SafetySharp.ITracing.logForwardTracesOfOrigins ()
                do! SafetySharp.ITracing.removeTracing ()
                do! SafetySharp.Analysis.Modelchecking.Prism.ExportPrismAstToFile.workflow ()
                let! result = getState ()
                let resultDecorated = (outputstyle.Section "Prism from Gwa-Model") + (outputstyle.TsamSource result)
                return resultDecorated
            }

            let outputWorkflow = workflow {
                let! output_III_1 = output_III_1_wf ()
                let! output_III_2 = output_III_2_wf ()
                let! output_III_3 = output_III_3_wf ()
                let! output_III_4 = output_III_4_wf ()
                let! output_III_5 = output_III_5_wf ()
                let! output_III_6 = output_III_6_wf ()
                let! output_III_7 = output_III_7_wf ()
                return output_III_1 + output_III_2 + output_III_3 + output_III_4 + output_III_5 + output_III_6 + output_III_7
            }
            runWorkflow_getResult outputWorkflow



                    
        let completeOutput : string =
            let content = sprintf "%s%s%s" output_I_complete output_II_complete output_III_complete
            outputstyle.Content content
        do SafetySharp.FileSystem.WriteToAsciiFile path completeOutput
        completeOutput

        
    let texOutput : OutputStyleDecorator =
        let texTemplateAsString = """
\documentclass[a4paper, 12pt,titlepage]{scrartcl}

\usepackage{tikz}
\usetikzlibrary{arrows,shapes}

%% Needs Python2 and dot2tex
%% You can install dot2tex with "pip install dot2tex" (even on Windows)
\usepackage{dot2texi}
\usepackage{listings}
\lstset{
	frame=single,
	breaklines=true
}
\begin{document}
%s
\end{document}
"""
        let sourceDecoratorTemplateAsString = "\n{\\scriptsize\n\\begin{lstlisting}\n%s\n\\end{lstlisting}\n}\n"
        let graphDecoratorTemplateAsString = "\n\\begin{tikzpicture}[>=latex',scale=0.5]\n\\begin{dot2tex}[dot,tikz,options=-s -tmath]\n%s\\end{dot2tex}.\n\\end{tikzpicture}\n"

        let contentDecoration (content:string) = 
            let texTemplate = Printf.StringFormat<_,string>(texTemplateAsString)
            sprintf texTemplate content        
        let sectionDecoration (chapterName:string) =
            sprintf "\\section{%s}\n" chapterName
        let tsamSourceDecorator (tsamSource:string) =
            let sourceDecoratorTemplate = Printf.StringFormat<_,string>(sourceDecoratorTemplateAsString)
            sprintf sourceDecoratorTemplate tsamSource
        let graphDecorator (graph:string) =
            let graphDecoratorTemplate = Printf.StringFormat<_,string>(graphDecoratorTemplateAsString)
            sprintf graphDecoratorTemplate graph
        {
            OutputStyleDecorator.Content = contentDecoration
            OutputStyleDecorator.Section = sectionDecoration;
            OutputStyleDecorator.TsamSource = tsamSourceDecorator;
            OutputStyleDecorator.Graph = graphDecorator;
        }
        
    let generateTexFile = generateFile texOutput


    
    let htmlOutput : OutputStyleDecorator =
        let htmlTemplateAsString = """<!DOCTYPE html>
<html>
  <head>
    <title>Report</title>
	<link rel="stylesheet" href="css/style.css" type="text/css">
    <!-- graphviz.js by mdaines from https://github.com/mdaines/viz.js (emscripten version of graphviz)-->
    <script src="lib/graphviz.js"></script>
    <script src="lib/codemirror.js"></script>
    <script src="lib/jquery-2.1.4.min.js"></script>

    <link rel="stylesheet" href="lib/codemirror.css">
  </head>
  <body>
  %s
  <script type="text/javascript">
      $(".graph").each(function(index) {
          var dotSource = $(".graphSource",this).html();
          var svgPicture = Viz(dotSource, "svg");
          //console.log(dotSource);
          $(this).html(svgPicture);
      } );
      $(".tsamSource").each(function(index) {
        CodeMirror.fromTextArea(this);
      } )
  </script>
  </body>
</html>
"""
        let sourceDecoratorTemplateAsString = """
    <form>
      <textarea class="tsamSource">%s</textarea>
    </form>
"""
        let graphDecoratorTemplateAsString = """
    <div class="graph">
      <script type="text/vnd.graphviz" class="graphSource">
%s
      </script>
    </div>
"""

        let contentDecoration (content:string) = 
            let htmlTemplate = Printf.StringFormat<_,string>(htmlTemplateAsString)
            sprintf htmlTemplate content
        let sectionDecoration (chapterName:string) = sprintf "    <h2>%s</h2>\n" chapterName
        let tsamSourceDecorator (tsamSource:string) =
            let sourceDecoratorTemplate = Printf.StringFormat<_,string>(sourceDecoratorTemplateAsString)
            sprintf sourceDecoratorTemplate tsamSource
        let graphDecorator (graph:string) =
            let graphDecoratorTemplate = Printf.StringFormat<_,string>(graphDecoratorTemplateAsString)
            sprintf graphDecoratorTemplate graph
        {
            OutputStyleDecorator.Content = contentDecoration
            OutputStyleDecorator.Section = sectionDecoration;
            OutputStyleDecorator.TsamSource = tsamSourceDecorator;
            OutputStyleDecorator.Graph = graphDecorator;
        }

    let generateHtmlFile = generateFile htmlOutput

open NUnit.Framework

[<TestFixture>]
module TsamToReportTexTest =
    open SafetySharp.Workflow
    
    // NOTE: Make sure, we use the same F#-version as the SafetySharp Project. Otherwise it cannot be started. See App.config for details
    
    [<Test>]
    let testWithSmokeTest8 () =        
        let useOnlyStochastic = false
        let path = "../../"
        
        let output = TsamToReport.generateTexFile useOnlyStochastic (path+"/Tex/smokeTest8.tex") (path + "/../../../../Examples/SAM/smokeTest8.sam")
        printfn "%s" output
        let output = TsamToReport.generateHtmlFile useOnlyStochastic (path+"/html/smokeTest8.html") (path + "/../../../../Examples/SAM/smokeTest8.sam")
        printfn "%s" output
        ()

    [<Test>]
    let testWithSmokeTest9 () =        
        let useOnlyStochastic = false
        let path = "../../"
        
        let output = TsamToReport.generateTexFile useOnlyStochastic (path+"/Tex/smokeTest9.tex") (path + "/../../../../Examples/SAM/smokeTest9.sam")
        printfn "%s" output
        let output = TsamToReport.generateHtmlFile useOnlyStochastic (path+"/html/smokeTest9.html") (path + "/../../../../Examples/SAM/smokeTest9.sam")
        printfn "%s" output
        ()

    [<Test>]
    let testWithSmokeTest10 () =        
        let useOnlyStochastic = false
        let path = "../../"
        
        let output = TsamToReport.generateTexFile useOnlyStochastic (path+"/Tex/smokeTest10.tex") (path + "/../../../../Examples/SAM/smokeTest10.sam")
        printfn "%s" output
        let output = TsamToReport.generateHtmlFile useOnlyStochastic (path+"/html/smokeTest10.html") (path + "/../../../../Examples/SAM/smokeTest10.sam")
        printfn "%s" output
        ()

    [<Test>]
    let testWithSmokeTest24 () =        
        let useOnlyStochastic = false
        let path = "../../"
        
        let output = TsamToReport.generateTexFile useOnlyStochastic (path+"/Tex/smokeTest24.tex") (path + "/../../../../Examples/SAM/smokeTest24.sam")
        printfn "%s" output
        let output = TsamToReport.generateHtmlFile useOnlyStochastic (path+"/html/smokeTest24.html") (path + "/../../../../Examples/SAM/smokeTest24.sam")
        printfn "%s" output
        ()

    [<Test>]
    let testWithSmokeTest25 () =        
        let useOnlyStochastic = false
        let path = "../../"
        
        let output = TsamToReport.generateTexFile useOnlyStochastic (path+"/Tex/smokeTest25.tex") (path + "/../../../../Examples/SAM/smokeTest25.sam")
        printfn "%s" output
        let output = TsamToReport.generateHtmlFile useOnlyStochastic (path+"/html/smokeTest25.html") (path + "/../../../../Examples/SAM/smokeTest25.sam")
        printfn "%s" output
        ()