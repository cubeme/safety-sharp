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

namespace SafetySharp.Models

// Preamble
// A passive form of a SAM-Model is a model which makes for every variable _at most one_ assignment. In those cases
// the assignment "x:=E" can be replaced by a simple assertion "assert x=E".
// The passive form allows the creation of verification condition algorithms which avoid an exponential size of these verification conditions.
// The paper
//  * [FS01] Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions.
//                http://dx.doi.org/10.1145/360204.360220
// introduced this passive form, which is very related to the "static single assignment form" (SSA form) or the "dynamic single assignment form" (DSA form) used in
// compiler optimization. They are essentially the same but do not handle indeterministic guarded commands.
// The paper
//  *  [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904
// describes two transformations to passive form. We implement the proposed one, which is version-optimal (has the least possible
// number of fresh variables for each old variable).
    


// Implementation of
//  * [FS01] Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions. http://dx.doi.org/10.1145/360204.360220

// NOTE: NOT TESTED!!!
// TODO: Implement treatment of local vars

// Advantage of this algorithm:
//   * smaller formulas
//   * seems to be faster for Sat/SMT-Solvers
//   * easier to verify interactively
// Disadvantages of this algorithm:
//   * more variables (artificial variables get introduced)


module internal TsamPassiveFormFS01 =
    open SafetySharp.Models.SamHelpers
    open Tsam
    open TsamHelpers
            
    type Substitutions =
        {
            IsBottom : bool;
            CurrentSubstitution : Map<Var,Expr>;
            NextGlobal : Map<Var,Var>;
            LocalTakenNames : Set<string>;
            VarToType : Map<Var,Type>;
             // Note: the elements, where ref points to, stays the same, when copied. No need to merge here!
            GlobalTakenNamesWithTypes : Map<Var,Type> ref;
            GlobalTakenNames : Set<string> ref;
            VarToCounter : Map<Var,int> ref;
            TryToRecycle : bool; // if true, we try to recycle currently unused variables
        }
            with
                static member initial (globalVars:(Var*Type) list) (localVars:(Var*Type) list) =
                    let localAndGlobalVars = localVars @ globalVars
                    let takenNamesAsString =
                        localAndGlobalVars |> List.map (fun (var,_type) -> var.getName)
                                           |> Set.ofList

                    {
                        Substitutions.IsBottom = false;
                        Substitutions.CurrentSubstitution =
                            let globalSubstitutions = globalVars |> List.fold (fun (acc:Map<Var,Expr>) (var,_type) -> acc.Add(var,Expr.Read(var))) Map.empty<Var,Expr>
                            let localAndGlobalSubstitutions = localVars |> List.fold (fun (acc:Map<Var,Expr>) (var,_type) -> acc.Add(var,Expr.Literal(_type.getDefaultValue))) globalSubstitutions
                            localAndGlobalSubstitutions
                        Substitutions.NextGlobal  =
                            globalVars |> List.map (fun (var,_type) -> (var,var))
                                       |> Map.ofList;                            
                        Substitutions.LocalTakenNames = takenNamesAsString
                        Substitutions.VarToType  =
                            localAndGlobalVars |> Map.ofList
                        Substitutions.GlobalTakenNamesWithTypes =
                            ref (localAndGlobalVars |> Map.ofList)
                        Substitutions.GlobalTakenNames = ref (takenNamesAsString)
                        Substitutions.VarToCounter =
                            let newMapLocals =
                                localVars |> List.map (fun (var,_) -> (var,0))
                                          |> Map.ofList;            
                            let newMapGlobals =
                                globalVars |> List.map (fun (var,_) -> (var,1))
                                           |> Map.ofList;            
                            let newMap = unionManyVarMaps [newMapLocals;newMapGlobals]
                            ref (newMap);
                        Substitutions.TryToRecycle = false;
                    }
                static member bottom =
                    {
                        Substitutions.IsBottom = true;
                        Substitutions.CurrentSubstitution = Map.empty<Var,Expr>;
                        Substitutions.NextGlobal = Map.empty<Var,Var>;
                        Substitutions.LocalTakenNames = Set.empty<string>;
                        Substitutions.VarToType = Map.empty<Var,Type>;
                        Substitutions.GlobalTakenNamesWithTypes = ref (Map.empty<Var,Type>)
                        Substitutions.GlobalTakenNames = ref (Set.empty<string>)
                        Substitutions.VarToCounter = ref (Map.empty<Var,int>);
                        Substitutions.TryToRecycle = true;
                    }
                    
                member this.tryToRecycleVar (_type:Type) : Var option =
                    // Recycled variables are variables, which have been used before in another indeterministic choice branch.
                    // We could try to get one of these to keep the state space small. This may or may not help to reduce the
                    // verification.
                    if this.TryToRecycle = false then
                        None
                    else
                        let unused =
                            Set.difference (this.GlobalTakenNames.Value) this.LocalTakenNames
                        let isOfCorrectType (name:string) : bool =
                            this.GlobalTakenNamesWithTypes.Value.Item (Var.Var(name)) =_type
                        unused |> Set.toList
                               |> List.tryPick (fun name -> if isOfCorrectType name then Some(Var.Var(name)) else None)
                        
                member this.getFreshVar (based_on:Var) : (Substitutions*Var) =
                    if this.VarToCounter.Value.Item based_on = 0 then
                        //variable has never been used, so use the current name and increase counter to one
                        let newSubstitutions =
                            { this with
                                Substitutions.CurrentSubstitution = this.CurrentSubstitution.Add(based_on,Expr.Read(based_on))
                            }
                        do this.VarToCounter := this.VarToCounter.Value.Add (based_on, 1)
                        (newSubstitutions,based_on)
                    else
                        let _type:Type = this.VarToType.Item based_on
                        match this.tryToRecycleVar (_type) with
                            | Some (_var) ->
                                let newSubstitutions =
                                    { this with
                                        Substitutions.CurrentSubstitution = this.CurrentSubstitution.Add(based_on,Expr.Read(_var))
                                        Substitutions.NextGlobal =
                                            if this.NextGlobal.ContainsKey based_on then
                                                this.NextGlobal.Add(based_on,_var) // only update for global vars
                                            else
                                                this.NextGlobal
                                    }
                                (newSubstitutions,_var)
                            | None ->
                                let currentCounter = this.VarToCounter.Value.Item based_on
                                do this.VarToCounter := this.VarToCounter.Value.Add (based_on,currentCounter + 1)
                                let nameCandidate = sprintf "%s_passive%i" based_on.getName currentCounter
                                let freshName = SafetySharp.FreshNameGenerator.namegenerator_c_like this.GlobalTakenNames.Value (nameCandidate)
                                let newVarWithFreshName = Var.Var(freshName)
                                let _type = this.VarToType.Item based_on
                                do this.GlobalTakenNames:=this.GlobalTakenNames.Value.Add (freshName)
                                do this.GlobalTakenNamesWithTypes:=this.GlobalTakenNamesWithTypes.Value.Add (newVarWithFreshName,_type)
                                let newSubstitutions =
                                    { this with
                                        Substitutions.LocalTakenNames = this.LocalTakenNames.Add (freshName);
                                        Substitutions.VarToType = this.VarToType.Add (newVarWithFreshName,_type);
                                        Substitutions.CurrentSubstitution = this.CurrentSubstitution.Add(based_on,Expr.Read(newVarWithFreshName));
                                        Substitutions.NextGlobal =
                                            if this.NextGlobal.ContainsKey based_on then
                                                this.NextGlobal.Add(based_on,newVarWithFreshName) // only update for global vars
                                            else
                                                this.NextGlobal
                                    }
                                (newSubstitutions,newVarWithFreshName)
                            

                static member merge (uniqueStatementIdGenerator:unit->StatementId) (subs:Substitutions list) : (Substitutions * (Stm list list)) =
                    //subs contains at least one member
                    
                    // merge is only possible, when the ref cells of GlobalTakenNames match
                    let numberedBranches = List.zip ([1..List.length subs]) subs
                    let deadBranches,livingBranches =
                        List.partition (fun (number,subs:Substitutions)->subs.IsBottom) numberedBranches
                    // we do not need to append or merge dead branches at all!
                    if livingBranches.Length = 0 then
                        //nothing is alive, so bottom!
                        let appendStatements =
                            deadBranches |> List.map (fun _ -> [])
                        (Substitutions.bottom,appendStatements)
                    else if livingBranches.Length = 1 then
                        // take the sub of the living branch.
                        // append no statement anywhere
                        let appendStatements =
                            numberedBranches |> List.map (fun _ -> [])
                        let number,livingBranch = livingBranches.Head
                        (livingBranch,appendStatements)
                    else
                        let (_,firstSub) = livingBranches.Head
                        let variablesToMerge = // this is the set "D" of figure 4 in the paper
                            let firstSub = firstSub.CurrentSubstitution
                            // Compare, if a sub maps to the same variable as firstSub does.
                            // If every sub has the same mapping as _firstSub_, they have _all_ same mapping.
                            // If they do not have all the same mapping, there is at least one sub, which
                            // has a different mapping than firstSub. That means comparing to firstSub is enough.
                            // There is no need to compare each pair of subs.
                            let compareEveryVarWithFirstSub (sub:Map<Var,Expr>) : Set<Var> =
                                //returns Vars not equal
                                sub |> Map.toList
                                    |> List.filter (fun (from,_to) -> (firstSub.Item from) <> _to )
                                    |> List.map (fun (from,_to) -> from)
                                    |> Set.ofList

                            livingBranches |> List.map ( fun (_,sub) -> sub.CurrentSubstitution)
                                           |> List.fold (fun toMerge sub -> Set.union toMerge (compareEveryVarWithFirstSub sub) ) Set.empty<Var>
                                           |> Set.toList //easier to process
                            
                        let mergedSubs =
                            // merge subs, such that it contains every locally created name (every name used in any branch should not be
                            // able to be recycled in the future)
                            let unifiedSubstitutions = livingBranches |> List.map (fun (_,subs) -> subs.CurrentSubstitution) |> unionManyVarMaps
                            let unifiedLocalTakenNames = livingBranches |> List.map (fun (_,subs) -> subs.LocalTakenNames) |> Set.unionMany
                            let unifiedVarToType = livingBranches |> List.map (fun (_,subs) -> subs.VarToType) |> unionManyVarMaps
                            { firstSub with
                                Substitutions.CurrentSubstitution = unifiedSubstitutions;
                                Substitutions.LocalTakenNames = unifiedLocalTakenNames;
                                Substitutions.VarToType = unifiedVarToType;
                            }
                        let (newSub) = // this calculates implicitly map "\Theta" of figure 4 in the paper
                            let createNewVariable (subst:Substitutions) (variable:Var) =
                                 let (newSub,var) = subst.getFreshVar variable
                                 newSub
                            variablesToMerge |> List.fold createNewVariable mergedSubs

                        let appendStatementsForLiving =
                            let appendsForSub (sub:Substitutions) : Stm list =                                          
                                let assumptionForVar (_var:Var) =
                                    let currentVar = sub.CurrentSubstitution.Item _var
                                    let nextVar = newSub.CurrentSubstitution.Item _var
                                    let newStatementId = uniqueStatementIdGenerator()
                                    Stm.Assume(newStatementId,Expr.BExpr(currentVar,BOp.Equals,nextVar)) 
                                variablesToMerge |> List.map assumptionForVar
                            livingBranches |> List.map (fun (number:int,sub) -> (number,appendsForSub sub))
                        let appendStatementsForDead : ((int*Stm list) list) =
                            deadBranches |> List.map (fun (number:int,_) -> number,[])
                        let appendStatements = // this is "R_a" or "R_b" generalized for lists of figure 4 in the paper
                            (appendStatementsForLiving @ appendStatementsForDead)
                                |> List.sortBy (fun (index,stmts) -> index)
                                |> List.map (fun (index,stmts) -> stmts)
                        (newSub,appendStatements)

                    // Note: output of the StatementsToAppend must be in the same order as the input!!!!
                    // if there is only one branch to merge, use it
                    // get, which variables are written to
                    
                    // TODO: One spontaneous idea to optimize (is almost a new algorithm):
                    //     * If the count, how many assignments are made to each variable in each branch,
                    //       we could save the number of last assignment to each variable in each branch.
                    //       When a fresh Variable is introduced for this last assignment, we use this fresh
                    //       variable in each branch for the last assignment. For every branch with no assignment
                    //       to this specific variable, we add "assume (lastVarAssignmentName=currentValue).
                    //       If there is only one branch, even this needs not to be done!
    
    let rec replaceVarsWithCurrentVars (sigma:Substitutions) (expr:Expr) : Expr =
        if sigma.IsBottom then
            expr
        else
            match expr with
                | Expr.Literal (_val) -> expr
                | Expr.Read (_var) ->
                    sigma.CurrentSubstitution.Item _var
                | Expr.ReadOld (_var) -> expr //old variables keep their value
                | Expr.UExpr (expr,uop) -> Expr.UExpr(replaceVarsWithCurrentVars sigma expr ,uop)
                | Expr.BExpr (left, bop, right) -> Expr.BExpr(replaceVarsWithCurrentVars sigma left,bop,replaceVarsWithCurrentVars sigma right)
        
    let rec passify (uniqueStatementIdGenerator:unit->StatementId) (sigma:Substitutions, stm:Stm) : (Substitutions*Stm) =
        match stm with
            | Stm.Assert (statementId,expr) ->
                let expr = replaceVarsWithCurrentVars sigma expr //need to do it with old sigma!
                if expr = Expr.Literal(Val.BoolVal(false)) then
                    (Substitutions.bottom,stm) //optimization: if false, then bottom
                else
                    (sigma,stm)
            | Stm.Assume (statementId,expr) ->
                let expr = replaceVarsWithCurrentVars sigma expr  //need to do it with old sigma!
                if expr = Expr.Literal(Val.BoolVal(false)) then
                    (Substitutions.bottom,stm) //optimization: if false, then bottom
                else
                    (sigma,stm)
            | Stm.Write (statementId,variable,expression) ->
                let expr = replaceVarsWithCurrentVars sigma expression  //need to do it with old sigma!
                let newSigma,newVar = sigma.getFreshVar variable
                (newSigma,Stm.Assume(statementId,Expr.BExpr(Expr.Read(newVar),BOp.Equals,expr)))
            | Stm.Block (statementId,statements) ->
                let newSigma,statementsRev =
                    let foldFct (sigma:Substitutions,statements:Stm list) (stm:Stm) =
                        if sigma.IsBottom then
                            (sigma,stm::statements) //nothing to do, the current block is already invalid (because there is one bottom in it)
                        else
                            let (newSigma,newStm) = passify uniqueStatementIdGenerator (sigma,stm)
                            (newSigma,newStm::statements)
                    List.fold foldFct (sigma,[]) statements
                (newSigma,Stm.Block(statementId,List.rev statementsRev))
            | Stm.Choice (statementId,choices) ->
                if choices = [] then
                    (sigma,Stm.Assume(statementId,Expr.Literal(Val.BoolVal(false))))
                else
                    let passifyChoice (choiceGuard:Expr option,choiceStm:Stm) : Substitutions*Stm =
                        let guardStm : Stm list =
                            if choiceGuard.IsSome then
                                //TODO: optimization missing
                                let assumeStmId = uniqueStatementIdGenerator ()
                                let assumeExpr = replaceVarsWithCurrentVars sigma choiceGuard.Value
                                let assumeStm = Stm.Assume(assumeStmId,assumeExpr)
                                [assumeStm]
                            else
                                []
                        let (sigma,choiceStm) = passify uniqueStatementIdGenerator (sigma,choiceStm)
                        let choiceStmWithGuard = choiceStm.prependStatements uniqueStatementIdGenerator guardStm
                        (sigma,choiceStmWithGuard)
                    let (sigmas,passifiedChoices) =
                        choices |> List.map passifyChoice
                                |> List.filter (fun (sigma,choice) -> not(sigma.IsBottom))
                                |> List.unzip
                    let (newSigma,stmtssToAppend) = Substitutions.merge uniqueStatementIdGenerator sigmas
                    let newChoices =
                        let appendStatements (passifiedChoice:Stm) stmtsToAppend =
                            (None,passifiedChoice.appendStatements uniqueStatementIdGenerator stmtsToAppend)
                        List.map2 appendStatements passifiedChoices stmtssToAppend
                    (newSigma,Stm.Choice (statementId,newChoices))
            | Stm.Stochastic (statementId,choices) ->
                assert (choices.IsEmpty=false)
                failwith "To be validated"
                // TODO: Is this really what we want?!?
                let passifyChoice (probability,stm) : Substitutions*(Expr*Stm) =
                    let probability = replaceVarsWithCurrentVars sigma probability
                    let (sigma,stm) = passify uniqueStatementIdGenerator (sigma,stm)
                    (sigma,(probability,stm))
                let (sigmas,passifiedChoices) =
                    choices |> List.map passifyChoice
                            |> List.filter (fun (sigma,choice) -> not(sigma.IsBottom))
                            |> List.unzip
                let (newSigma,stmtssToAppend) = Substitutions.merge uniqueStatementIdGenerator sigmas
                let newChoices =
                    let appendStatements (passifiedChoiceProb,passifiedChoiceStm:Stm) stmtsToAppend =
                        (passifiedChoiceProb,passifiedChoiceStm.appendStatements uniqueStatementIdGenerator stmtsToAppend)
                    List.map2 appendStatements passifiedChoices stmtssToAppend
                (newSigma,Stm.Stochastic (statementId,newChoices))
                    
    open SafetySharp.Workflow
    open SafetySharp.Models.SamHelpers

    let passifyPgm<'traceableOfOrigin>
            () : EndogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>> = workflow {
        do! TsamMutable.prependKeepValueAssignments ()
        let! state = getState ()
        let pgm = state.Pgm
        let globalVars = pgm.Globals |> List.map (fun gl -> gl.Var,gl.Type)
        let localVars= pgm.Locals |> List.map (fun lo -> lo.Var,lo.Type)
        let sigma = Substitutions.initial globalVars localVars
        let (newSigma,newBody) = passify (pgm.UniqueStatementIdGenerator) (sigma,pgm.Body)
        let newPgm =
            let createLocalVarDecl (_var,_type) = LocalVarDecl.createLocalVarDecl _var _type
            let oldGlobalsAsSet = pgm.Globals |> List.map (fun gl -> gl.Var) |> Set.ofList
            let newLocals =
                newSigma.VarToType |> Map.toList
                                   |> List.filter (fun (_var,_) -> not(oldGlobalsAsSet.Contains _var) ) // use only those variables, which are not in global
                                   |> List.map createLocalVarDecl
            { pgm with
                Pgm.Body = newBody;
                Pgm.Globals = pgm.Globals; // globals stay globals
                Pgm.Locals = newLocals;
                Pgm.NextGlobal = newSigma.NextGlobal;
                Pgm.CodeForm = CodeForm.Passive;
            }            
        let newState = {state with Pgm=newPgm}
        do! updateState newState
    }

    (*
    type SmallRefExampel =
        {
            Local : int;
            Global : int ref;
        }
            with
                static member init =
                    {
                        SmallRefExampel.Local = 1;
                        SmallRefExampel.Global = ref(1);
                    }
                member this.increase =
                    do this.Global := (!this.Global + 1);
                    { this with
                        SmallRefExampel.Local = this.Local + 1;
                    }
    let a1 = SmallRefExampel.init
    let a2 = a1
    let  b =  SmallRefExampel.init
    let  b' = b.increase
    let a1' = a1.increase
    let a2' = a1.increase
    printfn "%A" a1
    printfn "%A" a2
    printfn "%A" b
    printfn "%A" a1'
    printfn "%A" a2'
    printfn "%A" b'
    *)