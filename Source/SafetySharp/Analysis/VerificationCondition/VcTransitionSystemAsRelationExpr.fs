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

    open SafetySharp.Models.Tsam
    open SafetySharp.Models.SamHelpers
    open VcGuardWithAssignmentModel
    
    type TransitionSystem = {
        Globals : GlobalVarDecl list;
        VirtualNextVarToVar : Map<Var,Var>;
        VarToVirtualNextVar : Map<Var,Var>;
        Init : Expr;
        Trans : Expr;
    }
        

    let generateInitCondition (varDecls:GlobalVarDecl list) : Expr =
        let generateInit (varDecl:GlobalVarDecl) : Expr =
            let generatePossibleValues (initialValue : Val) : Expr =
                let assignVar = varDecl.Var
                let assignExpr = Expr.Literal(initialValue)
                let operator = BOp.Equals
                Expr.BExpr(Expr.Read(assignVar),operator,assignExpr)
            varDecl.Init |> List.map generatePossibleValues
                         |> createOredExpr
        varDecls |> List.map generateInit
                 |> createAndedExpr
    
    
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
        let createVirtualVarForVar (var:GlobalVarDecl) =
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
            TransitionSystem.VirtualNextVarToVar = virtualVarToVar;
            TransitionSystem.VarToVirtualNextVar = varToVirtualVar;
            TransitionSystem.Init = initExpr;
            TransitionSystem.Trans = transformedGwas;
        }

    
    (*
    let createVirtualVarEntriesForPgm (pgm:Pgm) : (Var*Var) list =
        // next( var_x) = NextGlobal( var_x).
        //TODO: Think about it. In SSA and Passive: last version is next version. That value could also be used as virtual var. Maybe no need to create a new one.
        //Var to Virtual Var which represents "next(Var)"
        let takenNames:Set<string> ref = 
            let localNames = pgm.Locals |> List.map (fun l -> l.Var.getName)
            let globalNames = pgm.Globals |> List.map (fun g -> g.Var.getName)
            (localNames @ globalNames) |> Set.ofList |> ref            
        let createNewName (based_on:Var) : string =
            let nameCandidate = sprintf "%s_virtual" based_on.getName
            let nameGenerator = SafetySharp.FreshNameGenerator.namegenerator_c_like
            let freshName = nameGenerator takenNames.Value (nameCandidate)
            takenNames:=takenNames.Value.Add(freshName)
            freshName        
        let createFreshVarsForNewVariableVersions (var:GlobalVarDecl) =
            let freshVar = Var.Var(createNewName var.Var)
            let nextGlobalVarOfVar = pgm.NextGlobal.Item (var.Var)
            (nextGlobalVarOfVar,freshVar)        
        let virtualVarEntries =
            pgm.Globals |> List.map createFreshVarsForNewVariableVersions
        virtualVarEntries
    *)
    
    (*
    problem here is, that the passive form requires local variables in the final model
    
    let transformTsamToTsareWithSp (pgm:Pgm) : TransitionSystem =
        // Program needs to be in passive form!
        // The way we implemented VcStrongestPostcondition.sp requires pgm to be in passive form
        if pgm.CodeForm <> CodeForm.Passive then
            failwith "program needs to be in passive form to use this algorithm"

        let virtualVarEntries = createVirtualVarEntries pgm
        let virtualVarToVar = virtualVarEntries |> List.map ( fun (var,virtVar) -> (virtVar,var)) |> Map.ofList
        let varToVirtualVar = virtualVarEntries |> Map.ofList
        
        let initExpr = generateInitCondition pgm.Globals
        
        let formulaForSPPrecondition =
            let createFormulaForGlobalVarDecl (globalVarDecl:GlobalVarDecl) : Expr =
                let varThatChanges = globalVarDecl.Var
                let varOld = varToVirtualVar.Item varCurrent
                let operator = Tsam.BOp.Equals
                Tsam.Expr.BExpr(Tsam.Expr.Read(varPost),operator,Tsam.Expr.Read(varCurrent))
            pgm.Globals |> List.map createFormulaForGlobalVarDecl
                        |> Tsam.createAndedExpr

        let transExpr = Expr.Literal(Val.BoolVal(true))
        {
            TransitionSystem.Globals = pgm.Globals;
            TransitionSystem.VirtualNextVarToVar = virtualVarToVar;
            TransitionSystem.VarToVirtualNextVar = varToVirtualVar;
            TransitionSystem.Init = initExpr;
            TransitionSystem.Trans = transExpr;
        }
    *)



    
    
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



