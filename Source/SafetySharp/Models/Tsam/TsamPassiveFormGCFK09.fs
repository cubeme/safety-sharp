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


// Implementation with the ideas of
//  *  [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904

// Advantage of this algorithm:
// Disadvantages of this algorithm:


// TODO: Switch ReadVersion to actually read versions and WriteVersion to actually written versions



module internal TsamPassiveFormGCFK09 =
    open SafetySharp.Models.SamHelpers
    open Tsam
    open TsamHelpers
    
    type StatementInfos =
        {
            ReadVersions : Map<int,Set<Var*int>> 
            WriteVersions : Map<int,Set<Var*int>>
            FirstRead : Map<int,Map<Var,int>>
            MaxLastWrite : Map<int,Map<Var,int>>
            Children : Map<int,Set<int>>
        }
            with
                static member initial =
                    {
                        StatementInfos.ReadVersions = Map.empty<int,Set<Var*int>>;
                        StatementInfos.WriteVersions = Map.empty<int,Set<Var*int>>;
                        StatementInfos.FirstRead = Map.empty<int,Map<Var,int>>
                        StatementInfos.MaxLastWrite = Map.empty<int,Map<Var,int>>
                        StatementInfos.Children = Map.empty<int,Set<int>>;
                    }
                    
    
    type CalculationCache =
        {
            StatementInfos : StatementInfos ref;
            MaxWriteOfPredecessor : Map<Var,int> // Var to MaxWriteOfPredecessorOfVar
            //NodesToRefresh : Set<int>
        }
            with
                static member initial (globalVars:Set<Var>) =
                    let maxWriteOfPredecessor =
                        // global fields have already been written to (in earlier steps or been initialized). Set the counter there to 1
                        globalVars |> Set.fold (fun (acc:Map<Var,int>) (elem:Var) -> acc.Add(elem,1)) Map.empty<Var,int>;
                    {
                        CalculationCache.StatementInfos = ref StatementInfos.initial
                        CalculationCache.MaxWriteOfPredecessor = maxWriteOfPredecessor;
                    }
                //static member maxWriteOfPredecessor_ToSetForm (maxWriteOfPredecessor:Map<Var,int>): Map<Var,Set<int>> =
                //    maxWriteOfPredecessor |> Map.map (fun key value -> Set.empty.Add value)
                
                member this.addEntryForStatement (sid:int) (readVersion:Set<Var*int>)
                                                           (writeVersion:Set<Var*int>)
                                                           (firstRead:Map<Var,int>)
                                                           (maxLastWrite:Map<Var,int>)
                                                           (children:Set<int>) : unit =
                    let statementInfos = this.StatementInfos.Value
                    this.StatementInfos :=
                        { statementInfos with                            
                            StatementInfos.ReadVersions = statementInfos.ReadVersions.Add(sid,readVersion)
                            StatementInfos.WriteVersions = statementInfos.WriteVersions.Add(sid,writeVersion)
                            StatementInfos.FirstRead = statementInfos.FirstRead.Add(sid,firstRead)
                            StatementInfos.MaxLastWrite = statementInfos.MaxLastWrite.Add(sid,maxLastWrite)
                            StatementInfos.Children = statementInfos.Children.Add(sid,children)
                        }
    
    let rec readsOfExpression (currentVersions:Map<Var,int>) (acc:Set<Var*int>) (expr:Expr) : Set<Var*int> =
        match expr with
            | Expr.Literal _ ->
                acc
            | Expr.Read (_var) ->                
                acc.Add( (_var,currentVersions.Item _var) )
            | Expr.ReadOld (_var) ->
                acc.Add( (_var,1) ) //initial version of a global field is 1
            | Expr.UExpr (expr,uop) ->
                readsOfExpression currentVersions acc expr
            | Expr.BExpr (left, bop, right) ->
                let readsOfLeft = readsOfExpression currentVersions acc left
                let readsOfRight = readsOfExpression currentVersions acc right
                Set.union readsOfLeft readsOfRight


    let rec calculateStatementInfosAcc (stmPath:int list) (sigma:CalculationCache) (stm:Stm) : CalculationCache =
        // This function is not side-effect-free. It is only intended as Worker for calculateStatementInfos, which provides
        // an immutable interface
        // afterwards sigma.StatementInfos contains all necessary information
        match stm with
            | Stm.Assert (sid,expr) ->
                let sid = sid.Value
                let read = readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Var*int> expr
                let write = Set.empty<Var*int>
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite = sigma.MaxWriteOfPredecessor
                let children = (Set.empty<int>)
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children
                sigma
            | Stm.Assume (sid,expr) ->
                let sid = sid.Value
                let read = readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Var*int> expr
                let write = Set.empty<Var*int>
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite = sigma.MaxWriteOfPredecessor
                let children = (Set.empty<int>)
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children
                sigma
            | Stm.Write (sid,variable,expression) ->
                let sid = sid.Value
                let read = readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Var*int> expression
                let writeVersion =
                    if sigma.MaxWriteOfPredecessor.ContainsKey variable then
                        let oldVersion = sigma.MaxWriteOfPredecessor.Item variable
                        oldVersion + 1
                    else
                        1 // first time written to variable
                let write = Set.empty<Var*int>.Add( (variable,writeVersion) )
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite =
                    sigma.MaxWriteOfPredecessor.Add(variable,writeVersion)                    
                let children = (Set.empty<int>)
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children                
                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma
            | Stm.Block (sid,statements) ->
                let sid = sid.Value
                let newSigmaAfterStatements =
                    List.fold (calculateStatementInfosAcc (sid::stmPath)) sigma statements
                let children =
                    statements |> List.map (fun stm -> stm.GetStatementId.Value) |> Set.ofList
                
                let statementInfos = newSigmaAfterStatements.StatementInfos.Value
                let read =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Var*int>
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Var*int>
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite = newSigmaAfterStatements.MaxWriteOfPredecessor
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children

                let newSigma =
                    { newSigmaAfterStatements with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma
            | Stm.Choice (sid,choices) ->
                let sid = sid.Value       
                let newSigmas =
                    choices |> List.map (calculateStatementInfosAcc (sid::stmPath) sigma)                    
                let children =
                    choices |> List.map (fun stm -> stm.GetStatementId.Value) |> Set.ofList
                                                                    
                let statementInfos = sigma.StatementInfos.Value
                let read =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Var*int>
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Var*int>
                let firstRead = sigma.MaxWriteOfPredecessor                
                let maxLastWrite =
                    let addToMapIfValueHigher (entries:Map<Var,int>) (_var:Var,version:int) : Map<Var,int> =
                        if (entries.ContainsKey _var) && (entries.Item _var >= version) then
                            entries
                        else
                            entries.Add(_var,version)
                    newSigmas |> List.collect (fun (sigma:CalculationCache) -> sigma.MaxWriteOfPredecessor |> Map.toList)
                              |> List.fold addToMapIfValueHigher Map.empty<Var,int>

                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children

                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma
            | Stm.Stochastic (sid,stochasticChoices) ->
                // Adapted code of Stm.Choice
                // Be careful: This node also reads stuff in its expression. But currently these expressions should only contain
                // combinations of Literals. But to be future proof, we also add reads of the probabilistic Expressions.
                let readsOfProbabilistic =
                    stochasticChoices |> List.map (fun (stochasticChoiceExpr,_) -> readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Var*int> stochasticChoiceExpr)
                                      |> Set.unionMany

                let sid = sid.Value       
                let newSigmas =
                    stochasticChoices |> List.map (fun (_,stochaticChoiceStm) -> calculateStatementInfosAcc (sid::stmPath) sigma stochaticChoiceStm)
                let children =
                    stochasticChoices |> List.map (fun (_,stochaticChoiceStm) -> stochaticChoiceStm.GetStatementId.Value) |> Set.ofList
                                                                    
                let statementInfos = sigma.StatementInfos.Value
                let read =
                    // be careful: This node also reads stuff in its expression
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Var*int>
                             |> Set.union readsOfProbabilistic
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Var*int>
                let firstRead = sigma.MaxWriteOfPredecessor                
                let maxLastWrite =
                    let addToMapIfValueHigher (entries:Map<Var,int>) (_var:Var,version:int) : Map<Var,int> =
                        if (entries.ContainsKey _var) && (entries.Item _var >= version) then
                            entries
                        else
                            entries.Add(_var,version)
                    newSigmas |> List.collect (fun (sigma:CalculationCache) -> sigma.MaxWriteOfPredecessor |> Map.toList)
                              |> List.fold addToMapIfValueHigher Map.empty<Var,int>

                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children

                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma

    let calculateStatementInfos (pgm:Pgm) : StatementInfos =
        // the returned StatementInfos is immutable        
        let globalVars = pgm.Globals |> List.map (fun g -> g.Var) |> Set.ofList
        let cacheWithGlobals = CalculationCache.initial globalVars

        let resultingCache = calculateStatementInfosAcc [] cacheWithGlobals pgm.Body
        resultingCache.StatementInfos.Value
    
    
    let createVariablePerVariableVersion (statementInfos:StatementInfos) (pgm:Pgm) : Map<Var*int,Var> =
        // get written versions of the root node
        let writeVersionsOfRoot = statementInfos.WriteVersions.Item pgm.Body.GetStatementId.Value
        let readVersionsOfRoot = statementInfos.ReadVersions.Item pgm.Body.GetStatementId.Value
        let initialVersions =
            // Otherwise, if the initial version of a variable is never read, it does not appear in the set varVersionTuple.
            // But it might be necessary for the missing statements. (See smokeTest6.sam)
            pgm.Globals |> List.map (fun gl -> (gl.Var,1) ) |> Set.ofList
        let varVersionTuples =
            (Set.unionMany [writeVersionsOfRoot;readVersionsOfRoot;initialVersions]) |> Set.toList
        
        let takenNames:Set<string> ref = 
            let localNames = pgm.Locals |> List.map (fun l -> l.Var.getName)
            let globalNames = pgm.Globals |> List.map (fun g -> g.Var.getName)
            (localNames @ globalNames) |> Set.ofList |> ref
        
        let createNewName (based_on:Var) (version:int) : string =
            let nameCandidate = sprintf "%s_passive%i" based_on.getName version
            let freshName = SafetySharp.FreshNameGenerator.namegenerator_c_like takenNames.Value (nameCandidate)
            takenNames:=takenNames.Value.Add(freshName)
            freshName
        
        let createFreshVarsForNewVariableVersions (var:Var,version:int) =
            if version = 1 then
                // keep, no need for first version to create a new variable
                ((var,version),var)
            else
                let freshVar = Var.Var(createNewName var version)
                ((var,version),freshVar)
        
        let newMap =
            varVersionTuples |> List.map createFreshVarsForNewVariableVersions |> Map.ofList
        newMap
    
        
    let rec replaceVarInExpr (readVersions:Map<Var,int>) (versionedVarToFreshVar:Map<Var*int,Var>) (expr:Expr) : Expr =
        match expr with
            | Expr.Literal (_) ->
                expr
            | Expr.Read (_var) ->                
                let _newVar =
                    let readVersionOfVar = readVersions.Item _var
                    versionedVarToFreshVar.Item (_var,readVersionOfVar)
                Expr.Read (_newVar)
            | Expr.ReadOld (_var) ->
                expr //old variables keep their value. TODO: Write Smoketest
            | Expr.UExpr (expr,uop) ->
                Expr.UExpr (replaceVarInExpr readVersions versionedVarToFreshVar expr,uop)
            | Expr.BExpr (left, bop, right) ->
                Expr.BExpr (replaceVarInExpr readVersions versionedVarToFreshVar left, bop, replaceVarInExpr readVersions versionedVarToFreshVar right)

    let rec replaceVarInStm (statementInfos:StatementInfos) (versionedVarToFreshVar:Map<Var*int,Var>) (stm:Stm) : Stm =
        match stm with
            | Stm.Assert (sid,expr) ->
                let readVersions = statementInfos.FirstRead.Item sid.Value
                Stm.Assert(sid,replaceVarInExpr readVersions versionedVarToFreshVar expr)
            | Stm.Assume (sid,expr) ->
                let readVersions = statementInfos.FirstRead.Item sid.Value
                Stm.Assume (sid,replaceVarInExpr readVersions versionedVarToFreshVar expr)
            | Stm.Block (sid,statements) ->
                let newStmnts = statements |> List.map (replaceVarInStm statementInfos versionedVarToFreshVar)
                Stm.Block (sid,newStmnts)
            | Stm.Choice (sid,choices) ->
                let newChoices = choices |> List.map (replaceVarInStm statementInfos versionedVarToFreshVar)
                Stm.Choice (sid,newChoices)
            | Stm.Stochastic (sid,stochasticChoices) ->
                let readVersions = statementInfos.FirstRead.Item sid.Value
                let rewriteChoice (stochasticExpr,stochasticStm) =
                    let newStochasticExpr = replaceVarInExpr readVersions versionedVarToFreshVar stochasticExpr
                    let newStochasticStm = replaceVarInStm statementInfos versionedVarToFreshVar stochasticStm
                    (newStochasticExpr,newStochasticStm)
                let newChoices = stochasticChoices |> List.map rewriteChoice
                Stm.Stochastic (sid,newChoices)
            | Stm.Write (sid,_var,expr) ->
                let writeVersions = statementInfos.MaxLastWrite.Item sid.Value
                let readVersions = statementInfos.FirstRead.Item sid.Value
                let _newVar =
                    let writeVersionOfVar = writeVersions.Item _var
                    versionedVarToFreshVar.Item (_var,writeVersionOfVar)
                Stm.Write (sid,_newVar,replaceVarInExpr readVersions versionedVarToFreshVar expr)
        
    let rec addMissingAssignmentsBeforeMerges (statementInfos:StatementInfos) (uniqueStatementIdGenerator : unit -> StatementId) (versionedVarToFreshVar:Map<Var*int,Var>) (stm:Stm) : Stm =
        match stm with
            | Stm.Assert (sid,expr) ->
                stm
            | Stm.Assume (sid,expr) ->
                stm
            | Stm.Block (sid,statements) ->
                let newStmnts = statements |> List.map (addMissingAssignmentsBeforeMerges statementInfos uniqueStatementIdGenerator versionedVarToFreshVar)
                Stm.Block (sid,newStmnts)
            | Stm.Choice (sid,choices) ->
                let newChoices = choices |> List.map (addMissingAssignmentsBeforeMerges statementInfos uniqueStatementIdGenerator versionedVarToFreshVar)                
                let readOfNextNode = statementInfos.MaxLastWrite.Item sid.Value
                //Note: maxLastWrite of this statement is firstRead of next Statement. Thus we still check the formula int the paper.
                do printfn "%+A" (sid.Value)
                let addMissingAssignmentsToBranch (branch:Stm) : Stm =
                    let missingStatementsOfBranch =
                        let maxLastWriteOfBranch = statementInfos.MaxLastWrite.Item branch.GetStatementId.Value
                        let createAssignment (_var:Var,nextReadVersion:int,writeVersionOfBranch:int) =
                            let freshStatementId = uniqueStatementIdGenerator ()
                            let assignTo = versionedVarToFreshVar.Item (_var,nextReadVersion)
                            let assignExpr = Expr.Read(versionedVarToFreshVar.Item (_var,writeVersionOfBranch))
                            Stm.Write(freshStatementId,assignTo,assignExpr)                            
                        readOfNextNode |> Map.toList
                                       |> List.map (fun (_var,nextReadVersion ) -> (_var,nextReadVersion, maxLastWriteOfBranch.Item _var ) )
                                       |> List.filter (fun (_var,nextReadVersion , writeVersionOfBranch) -> nextReadVersion<>writeVersionOfBranch )
                                       |> List.map createAssignment
                    branch.appendStatements uniqueStatementIdGenerator missingStatementsOfBranch
                // check each new branch
                let newChoices =
                    newChoices |> List.map addMissingAssignmentsToBranch
                Stm.Choice (sid,newChoices)
            | Stm.Stochastic (sid,stochasticChoices) ->
                // adapted just code of Stm.Choice
                let recursiveAddMissing (stochasticExpr,stochasticStm) =
                    let newStochasticStm = addMissingAssignmentsBeforeMerges statementInfos uniqueStatementIdGenerator versionedVarToFreshVar stochasticStm
                    (stochasticExpr,newStochasticStm)
                let newChoices = stochasticChoices |> List.map recursiveAddMissing                
                let readOfNextNode = statementInfos.MaxLastWrite.Item sid.Value
                //Note: maxLastWrite of this statement is firstRead of next Statement. Thus we still check the formula int the paper.
                let addMissingAssignmentsToBranch (branch:Stm) : Stm =
                    let missingStatementsOfBranch =
                        let maxLastWriteOfBranch = statementInfos.MaxLastWrite.Item branch.GetStatementId.Value
                        let createAssignment (_var:Var,nextReadVersion:int,writeVersionOfBranch:int) =
                            let freshStatementId = uniqueStatementIdGenerator ()
                            let assignTo = versionedVarToFreshVar.Item (_var,nextReadVersion)
                            let assignExpr = Expr.Read(versionedVarToFreshVar.Item (_var,writeVersionOfBranch))
                            Stm.Write(freshStatementId,assignTo,assignExpr)                            
                        readOfNextNode |> Map.toList
                                       |> List.map (fun (_var,nextReadVersion ) -> (_var,nextReadVersion, maxLastWriteOfBranch.Item _var ) )
                                       |> List.filter (fun (_var,nextReadVersion , writeVersionOfBranch) -> nextReadVersion<>writeVersionOfBranch )
                                       |> List.map createAssignment
                    branch.appendStatements uniqueStatementIdGenerator missingStatementsOfBranch
                // check each new branch
                let newChoices =
                    newChoices |> List.map (fun (stochasticExpr,stochasticStm) -> (stochasticExpr,addMissingAssignmentsToBranch stochasticStm))
                Stm.Stochastic (sid,newChoices)
            | Stm.Write (sid,_var,expr) ->
                stm
                
    let rec replaceAssignmentByAssumption (stm:Stm) : Stm =
        // Note: take care, each variable is only written _once_. TODO: Implement check
        match stm with
            | Stm.Assert (sid,expr) ->
                stm
            | Stm.Assume (sid,expr) ->
                stm
            | Stm.Block (sid,statements) ->
                let newStmnts = statements |> List.map replaceAssignmentByAssumption
                Stm.Block (sid,newStmnts)
            | Stm.Choice (sid,choices) ->
                let newChoices = choices |> List.map replaceAssignmentByAssumption
                Stm.Choice (sid,newChoices)
            | Stm.Stochastic (sid,stochasticChoices) ->
                let newChoices = stochasticChoices |> List.map (fun (stochasticExpr,stochasticStm) -> (stochasticExpr,replaceAssignmentByAssumption stochasticStm))
                Stm.Stochastic (sid,newChoices)
            | Stm.Write (sid,_var,expr) ->
                Stm.Assume(sid,Expr.BExpr(Expr.Read(_var),BOp.Equals,expr))

    open SafetySharp.Workflow
    open SafetySharp.Models.SamHelpers
    
    let transformProgramToSsaForm_Original<'traceableOfOrigin>
            () : EndogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let pgm = state.Pgm
        let globalVars = pgm.Globals |> List.map (fun gl -> gl.Var,gl.Type)
        let localVars= pgm.Locals |> List.map (fun lo -> lo.Var,lo.Type)
        
        let statementInfos = calculateStatementInfos pgm

        let versionedVarToFreshVar = createVariablePerVariableVersion statementInfos pgm
        // replace versionedVar by fresh Var in each statement and expression
        let newBodyWithReplacedExprs = replaceVarInStm statementInfos versionedVarToFreshVar pgm.Body
        // Add Assignments. To add assignments, we need to introduce new statements. For that, we need new statement ids
        let newBodyWithoutMissingAssignments = addMissingAssignmentsBeforeMerges statementInfos pgm.UniqueStatementIdGenerator versionedVarToFreshVar newBodyWithReplacedExprs
        // statementInfos is now outdated
        
        let mappingToNextGlobal =
            //NextGlobal maps to each global variable var_i the variable var_j, which contains the value of var_i, after Body was executed. var_i can be var_j (substitution)
            let maxLastWriteOfRoot = statementInfos.MaxLastWrite.Item pgm.Body.GetStatementId.Value
            let globalVarSet = pgm.Globals |> List.map (fun gl -> gl.Var) |> Set.ofList
            maxLastWriteOfRoot |> Map.filter (fun var nextVarVersion -> globalVarSet.Contains var) //only use global vars and not local vars
                               |> Map.map (fun var nextVarVersion -> versionedVarToFreshVar.Item(var,nextVarVersion))
        // statementInfos is now useless
                
        let varToType =
            let localVarToType = pgm.Locals |> List.map (fun l -> l.Var,l.Type)
            let globalVarToType = pgm.Globals |> List.map (fun g -> g.Var,g.Type)
            (localVarToType @ globalVarToType) |> Map.ofList


        let newPgm =
            let createLocalVarDecl (_var,_type) = LocalVarDecl.createLocalVarDecl _var _type
            let oldGlobalsAsSet = pgm.Globals |> List.map (fun gl -> gl.Var) |> Set.ofList
            let newLocals =
                let newVersions =
                    versionedVarToFreshVar |> Map.toList
                                           |> List.filter (fun ((_var1,version),_var2) -> _var1 <> _var2)
                                           |> List.map (fun ((_var1,version),_var2) -> createLocalVarDecl (_var2,varToType.Item _var1) ) 
                (newVersions @ pgm.Locals)
            { pgm with
                Pgm.Body = newBodyWithoutMissingAssignments;
                Pgm.Globals = pgm.Globals; // globals stay globals
                Pgm.Locals = newLocals;
                Pgm.CodeForm = CodeForm.SingleAssignments;
                Pgm.NextGlobal = mappingToNextGlobal;
            }            
        let newState = {state with Pgm=newPgm}
        do! updateState newState
    }



    //to Passive Form: 
    let transformProgramToPassiveForm_Original<'traceableOfOrigin>
            () : EndogenousWorkflowFunction<TsamMutable.MutablePgm<'traceableOfOrigin>> = workflow {
        do! transformProgramToSsaForm_Original ()
        let! state = getState ()
        let pgm = state.Pgm
        // Todo: checkEveryVariableWrittenAtMostOnce ()
        // replace all assignments by assumptions
        let newBody = replaceAssignmentByAssumption pgm.Body
        let newPgm =
            { pgm with
                Pgm.Body = newBody;
                Pgm.CodeForm = CodeForm.Passive;
            }
        let newState = {state with Pgm=newPgm}
        do! updateState newState
    }
        

    // TODO: Make this a bachelor thesis?
    // TODO: Write test programs, which check, if the model checker / smt solver returns for each expected input the expected output
    // TODO: Local optimizations of [GCFK09], which decrease the number of copies. (Proposed in this paper)
    // TODO: Local optimizations of [GCFK09], which makes the last write in a branch directly to the version needed. May need to look into subbranches. As last resort add assignment, if replacing a version is not possible. (own idea).
    // TODO: Local optimization which tries to create only as many variables as necessary for each _type_ (createVariablePerType). (own idea)
    // TODO: Optimization: If a Version is never read, we can omit the assignment :-D
