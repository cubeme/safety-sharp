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

namespace SafetySharp.Analysis.VerificationCondition

module internal TransitionSystemAsRelationExpr =
    // Tsare

    open SafetySharp.Models
    open SafetySharp.Models.SamHelpers
    open VcGuardWithAssignmentModel
    
    type VarDecl = Tsam.GlobalVarDecl
    type IvarDecl = Tsam.LocalVarDecl
    type Var = Tsam.Var
    type Val = Tsam.Val
    type BOp= Tsam.BOp
    type Expr = Tsam.Expr

    type TransitionSystem = {
        Globals : VarDecl list;
        Ivars : IvarDecl list;
        // The virtual next var should be purely virtual. In e.g. NuXmv it will be replaced by next(x). This variable should neither appear in
        // Globals nor in Ivars. Every Global should have a virtual next var
        VirtualNextVarToVar : Map<Var,Var>;
        VarToVirtualNextVar : Map<Var,Var>;
        Init : Expr;
        Trans : Expr;
    }

    open SafetySharp.ITracing
    
    type TransitionSystemTracer<'traceableOfOrigin> = {
        TransitionSystem : TransitionSystem;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Tsam.Traceable;
    }
        with
            interface ITracing<TransitionSystem,'traceableOfOrigin,Tsam.Traceable,TransitionSystemTracer<'traceableOfOrigin>> with
                member this.getModel = this.TransitionSystem
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Sam.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Sam.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : Tsam.Traceable list =
                    this.TransitionSystem.Globals |> List.map (fun varDecl -> Traceable.Traceable(varDecl.Var))

    type Traceable = Tsam.Traceable
        

    // -- COMMON ------------------------------------------------------

    let generateInitCondition (varDecls:VarDecl list) : Expr =
        let generateInit (varDecl:VarDecl) : Expr =
            let generatePossibleValues (initialValue : Val) : Expr =
                let assignVar = varDecl.Var
                let assignExpr = Expr.Literal(initialValue)
                let operator = BOp.Equals
                Expr.BExpr(Expr.Read(assignVar),operator,assignExpr)
            varDecl.Init |> List.map generatePossibleValues
                         |> TsamHelpers.createOredExpr
        varDecls |> List.map generateInit
                 |> TsamHelpers.createAndedExpr
    
    
    // -- GWAM --------------------------------------------------------
    
    let createVirtualVarEntriesForGwam (gwam:GuardWithAssignmentModel) : (Var*Var) list =
        //var_x,next(var_x).
        //Var to Virtual Var which represents "next(Var)"
        let takenNames:Set<string> ref = 
            let globalNames = gwam.Globals |> List.map (fun g -> g.Var.getName)
            (globalNames) |> Set.ofList |> ref            
        let createNewName (based_on:Var) : string =
            let nameCandidate = sprintf "%s_virtual" based_on.getName
            let nameGenerator = SafetySharp.FreshNameGenerator.namegenerator_c_like
            let freshName = nameGenerator takenNames.Value (nameCandidate)
            takenNames:=takenNames.Value.Add(freshName)
            freshName        
        let createVirtualVarForVar (var:VarDecl) =
            let virtualVar = Var.Var(createNewName var.Var)
            (var.Var,virtualVar)        
        let virtualVarEntries =
            gwam.Globals |> List.map createVirtualVarForVar
        virtualVarEntries

    let transformGwamToTsare (gwam:GuardWithAssignmentModel) : TransitionSystem =
        // The weakest precondition (backwards) makes indeterministic choice to "And" and "Assumes \phi;S" to "\phi => S".
        // The strongest postcondition (forward) makes an indeterministic choice to "Or" and "Assumes \phi;S" to "\phi And S".
        // There is a strong duality between these two. But they are different. See [Nafz12 page 218].
        // Because we make forward reasoning, we use the sp way.
                
        let virtualVarEntries = createVirtualVarEntriesForGwam gwam
        let virtualVarToVar = virtualVarEntries |> List.map ( fun (var,virtVar) -> (virtVar,var)) |> Map.ofList
        let varToVirtualVar = virtualVarEntries |> Map.ofList
        
        let initExpr = generateInitCondition gwam.Globals

        let transformGwa (gwa:GuardWithAssignments) =
            let transformAssignment (var:Var,expr:Expr) : Expr =
                Expr.BExpr(Expr.Read(varToVirtualVar.Item var),BOp.Equals,expr)
            let transformedAssignments =
                gwa.Assignments |> Map.toList
                                |> List.map transformAssignment                            
                                |> Expr.createAndedExpr //here make an "and"
            Expr.BExpr(gwa.Guard,BOp.And,transformedAssignments)
        let transformedGwas =
            gwam.GuardsWithFinalAssignments |> List.map transformGwa
                                            |> Expr.createOredExpr // the gwas are connected with an or                        
        {
            TransitionSystem.Globals = gwam.Globals;
            TransitionSystem.Ivars = [];
            TransitionSystem.VirtualNextVarToVar = virtualVarToVar;
            TransitionSystem.VarToVirtualNextVar = varToVirtualVar;
            TransitionSystem.Init = initExpr;
            TransitionSystem.Trans = transformedGwas;
        }

        
    // -- TSAM with strongest postcondition ----------------------------
    
    // This strongest postcondition transformation requires input variables
        
    let createVirtualVarEntryPool (pgm:Tsam.Pgm) : Map<Var,Var> =
        //var_x,next(var_x).
        //Var to Virtual Var which represents "next(Var)"
        let takenNames:Set<string> ref = 
            let globalNames = pgm.Globals |> List.map (fun g -> g.Var.getName)
            let localNames = pgm.Locals |> List.map (fun l -> l.Var.getName)
            (globalNames) |> Set.ofList |> ref            
        let createNewName (based_on:Var) : string =
            let nameCandidate = sprintf "%s_virtual" based_on.getName
            let nameGenerator = SafetySharp.FreshNameGenerator.namegenerator_c_like
            let freshName = nameGenerator takenNames.Value (nameCandidate)
            takenNames:=takenNames.Value.Add(freshName)
            freshName
        let createVirtualVarForVar (var:VarDecl) =
            let virtualVar = Var.Var(createNewName var.Var)
            (var.Var,virtualVar)        
        let virtualVarEntries =
            pgm.Globals |> List.map createVirtualVarForVar
        virtualVarEntries |> Map.ofList

    let transformTsamToTsareWithSp (pgm:Tsam.Pgm) : TransitionSystem =
        // Program needs to be in passive form!
        // The way we implemented VcStrongestPostcondition.sp requires pgm to be in passive form
        // Note: In the description below, pgm.next[x:Var] : Var is the map entry of pgm.NextGlobal
        if pgm.CodeForm <> Tsam.CodeForm.Passive then
            failwith "program needs to be in passive form to use this algorithm"

        let varToVirtualNextVarEntries,ivars =
            // Every global var needs a virtual next var for the transition system.
            // If there already exists a local variable, which contains the next value of this global variable,
            // we do not threat this variable as a global variable anymore (remove from ivars).
            // Otherwise we add a new virtual variable.
            let virtualVarPool = createVirtualVarEntryPool pgm            
            let ivarsComplete = pgm.Locals |> Set.ofList            
            let processGlobalVar (varToVirtualNextVarEntries:(Var*Var) list,ivars:Set<IvarDecl>) (gl:VarDecl) =
                if pgm.NextGlobal.Item gl.Var =  gl.Var then
                    // We need to create a new virtual var. we use one from the pool. Ivars needs no change
                    let newVirtualEntry =
                        virtualVarPool.Item gl.Var
                    let newEntry = (gl.Var,newVirtualEntry)
                    (newEntry::varToVirtualNextVarEntries,ivars)
                else
                    // pgm.next[x:Var] is a local var. We "change" this local var into the next value of the var x.
                    // Ivar needs a change: We remove the newEntry.
                    let newVirtualEntry =
                        pgm.NextGlobal.Item gl.Var
                    let newIvars = 
                        ivars.Remove ({IvarDecl.Type=gl.Type;IvarDecl.Var=newVirtualEntry;})
                    let newEntry = (gl.Var,newVirtualEntry)
                    (newEntry::varToVirtualNextVarEntries,newIvars)
            pgm.Globals |> List.fold processGlobalVar ([],ivarsComplete)

        let virtualNextVarToVar = varToVirtualNextVarEntries |> List.map ( fun (var,virtVar) -> (virtVar,var)) |> Map.ofList
        let varToVirtualNextVar = varToVirtualNextVarEntries |> Map.ofList
        
        let initExpr = generateInitCondition pgm.Globals
                
        let formulaForSPPrecondition =
            Expr.Literal(Val.BoolVal(true)) // we do not assume anything before                        
        let transExpr =
            // use strongest postcondition on program
            let passivePgmAsExpr,additionalProofObligations =
                VcStrongestPostcondition.sp (formulaForSPPrecondition,pgm.Body)
            // to add a connection between now and the next state, we add next(x) = pgm.next[x] for each global variable,
            // which was not changed. (When a variable was changed at least once, there is an entry in the passive program.)
            let globalNextExprList =
                let createEntry (globalVarWhichDoesNotChange,_) =
                    Expr.BExpr(Expr.Read(globalVarWhichDoesNotChange),BOp.Equals,Expr.Read(varToVirtualNextVar.Item globalVarWhichDoesNotChange))
                pgm.NextGlobal |> Map.toList
                               |> List.filter (fun (prev,next) -> prev=next)
                               |> List.map createEntry
            // add proof obligations, which come from Stm.Asserts
            let proofObligationsAsList = additionalProofObligations |> Set.toList
            // we "And" all three things and get our transExpr
            (passivePgmAsExpr::globalNextExprList@proofObligationsAsList) |> Expr.createAndedExpr
        // remove last version from ivar (if a version was created)
        let spOfPgm = VcStrongestPostcondition.sp
                                
        {
            TransitionSystem.Globals = pgm.Globals;
            TransitionSystem.Ivars = ivars |> Set.toList;
            TransitionSystem.VirtualNextVarToVar = virtualNextVarToVar;
            TransitionSystem.VarToVirtualNextVar = varToVirtualNextVar;
            TransitionSystem.Init = initExpr;
            TransitionSystem.Trans = transExpr;
        }
        
    // -- TSAM with weakest precondition ------------------------------    
    
    // Note:
    //  weakest precondition does only work in deterministic cases
    //    let formulaForWPPostcondition =
    //        // First Approach: "a'=a_last, b'<->b_last, ...."
    //        // THIS FORMULA IS WRONG. It only works for the deterministic case. SEE RESULTS OF smokeTest5.sam
    //        // The paper "To Goto Where No Statement Has Gone Before" offers in chapter 3 a way out.
    //        // Their goal is to transform "Code Expressions" (Code with statements) into genuine Expressions.
    //        let createFormulaForGlobalVarDecl (globalVarDecl:Tsam.GlobalVarDecl) : Tsam.Expr =
    //            let varCurrent = globalVarDecl.Var
    //            let varPost = nuXmvVariables.VarToVirtualVar.Item varCurrent
    //            let operator = Tsam.BOp.Equals
    //            Tsam.Expr.BExpr(Tsam.Expr.Read(varPost),operator,Tsam.Expr.Read(varCurrent))
    //        pgm.Globals |> List.map createFormulaForGlobalVarDecl
    //                    |> Tsam.createAndedExpr


        
    // -- Workflow ----------------------------------------------------
    open SafetySharp.Workflow

    let transformGwamToTsareWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<GuardWithAssignmentModelTracer<'traceableOfOrigin>,TransitionSystemTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let model = state.GuardWithAssignmentModel
        let transformed =
            {
                TransitionSystemTracer.TransitionSystem = transformGwamToTsare model;
                TransitionSystemTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                TransitionSystemTracer.ForwardTracer = state.ForwardTracer;
            }
        do! updateState transformed
    }   

    let transformTsamToTsareWithSpWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>,TransitionSystemTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let model = state.Pgm
        let transformed =
            {
                TransitionSystemTracer.TransitionSystem = transformTsamToTsareWithSp model;
                TransitionSystemTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                TransitionSystemTracer.ForwardTracer = state.ForwardTracer;
            }
        do! updateState transformed
    }
    