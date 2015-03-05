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
//  *  [GCFK09] Radu Grigore, Julien Charles, Fintan Fairmichael, Joseph Kiniry. Strongest Postcondition of Unstructured Programs.
//                 http://dx.doi.org/10.1145/1557898.1557904

// Advantage of this algorithm:
// Disadvantages of this algorithm:

module internal VcPassiveFormGCFK09 =
    open SafetySharp.Models.SamHelpers
    open VcSam
        
    type StatementInfos =
        {
            ReadVersion : Map<int,Map<Var,Set<int>>> // Node to [Var to [Set of ReadVersionNumber]]. 
            WriteVersion : Map<int,Map<Var,Set<int>>> // Node to [Var to [Set of WriteVersionNumber]].
            Children : Map<int,Set<int>> 
        }
            with
                static member initial =
                    {
                        StatementInfos.ReadVersion = Map.empty<int,Map<Var,Set<int>>>;
                        StatementInfos.WriteVersion = Map.empty<int,Map<Var,Set<int>>>;
                        StatementInfos.Children = Map.empty<int,Set<int>>;
                    }
    
    type CalculationCache =
        {
            StatementInfos : StatementInfos ref;
            MaxWriteOfPredecessor : Map<Var,int> // Var to MaxWriteOfPredecessorOfVar
            MaxWriteOfPredecessor_SetForm :  Map<Var,Set<int>> //to buffer the result.
        }
            with
                static member initial (globalVars:Set<Var>) =
                    let maxWriteOfPredecessor =
                        // global fields have already been written to (in earlier steps or been initialized). Set the counter there to 1
                        globalVars |> Set.fold (fun (acc:Map<Var,int>) (elem:Var) -> acc.Add(elem,1)) Map.empty<Var,int>;
                    {
                        CalculationCache.StatementInfos = ref StatementInfos.initial
                        CalculationCache.MaxWriteOfPredecessor = maxWriteOfPredecessor;
                        CalculationCache.MaxWriteOfPredecessor_SetForm = CalculationCache.maxWriteOfPredecessor_ToSetForm maxWriteOfPredecessor;
                    }
                static member maxWriteOfPredecessor_ToSetForm (maxWriteOfPredecessor:Map<Var,int>): Map<Var,Set<int>> =
                    maxWriteOfPredecessor |> Map.map (fun key value -> Set.empty.Add value)
                
                member this.addEntryForStatement (sid:int) (readVersion:Map<Var,Set<int>>) (writeVersion:Map<Var,Set<int>>) (children:Set<int>) : unit =
                    let statementInfos = this.StatementInfos.Value
                    this.StatementInfos :=
                        { statementInfos with                            
                            StatementInfos.ReadVersion = statementInfos.ReadVersion.Add(sid,readVersion)
                            StatementInfos.WriteVersion = statementInfos.WriteVersion.Add(sid,writeVersion)
                            StatementInfos.Children = statementInfos.Children.Add(sid,children)
                        }


    let rec calculateStatementInfosAcc (stmPath:int list) (sigma:CalculationCache) (stm:Stm) : CalculationCache =
        // This function is not side-effect-free. It is only intended as Worker for calculateStatementInfos, which provides
        // an immutable interface
        // afterwards sigma.StatementInfos contains all necessary information
        match stm with
            | Stm.Assert (sid,expr) ->
                let sid = sid.Value
                let read = sigma.MaxWriteOfPredecessor_SetForm
                let write = sigma.MaxWriteOfPredecessor_SetForm
                do sigma.addEntryForStatement sid read write (Set.empty<int>)
                sigma
            | Stm.Assume (sid,expr) ->
                let sid = sid.Value
                let read = sigma.MaxWriteOfPredecessor_SetForm
                let write = sigma.MaxWriteOfPredecessor_SetForm
                do sigma.addEntryForStatement sid read write (Set.empty<int>)
                sigma
            | Stm.Write (sid,variable,expression) ->
                let sid = sid.Value
                let read = sigma.MaxWriteOfPredecessor_SetForm
                let write =
                    if sigma.MaxWriteOfPredecessor.ContainsKey variable then
                        let oldVersion = sigma.MaxWriteOfPredecessor.Item variable
                        sigma.MaxWriteOfPredecessor.Add(variable,oldVersion+1)
                    else
                        sigma.MaxWriteOfPredecessor.Add(variable,1) // first time written to variable
                let write_SetForm = CalculationCache.maxWriteOfPredecessor_ToSetForm write
                do sigma.addEntryForStatement sid read write_SetForm (Set.empty<int>)
                
                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = write;
                        CalculationCache.MaxWriteOfPredecessor_SetForm = write_SetForm;
                    }
                newSigma
            | Stm.Block (sid,statements) ->
                let sid = sid.Value
                let newSigmaAfterStatements =
                    List.fold (calculateStatementInfosAcc (sid::stmPath)) sigma statements
                let children =
                    statements |> List.map (fun stm -> stm.GetStatementId.Value) |> Set.ofList
                
                let statementInfos = newSigmaAfterStatements.StatementInfos.Value
                let mergeEntries = mergeEntriesOfVarSetMap<int>
                let read =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersion.Item child)
                             |> Seq.fold mergeEntries Map.empty<Var,Set<int>>
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersion.Item child)
                             |> Seq.fold mergeEntries Map.empty<Var,Set<int>>                
                do newSigmaAfterStatements.addEntryForStatement sid read write children

                let newSigma =
                    { newSigmaAfterStatements with
                        CalculationCache.MaxWriteOfPredecessor = newSigmaAfterStatements.MaxWriteOfPredecessor;
                        CalculationCache.MaxWriteOfPredecessor_SetForm = newSigmaAfterStatements.MaxWriteOfPredecessor_SetForm;
                    }
                newSigma
            | Stm.Choice (sid,choices) ->
                let sid = sid.Value       
                let newSigmas =
                    choices |> List.map (calculateStatementInfosAcc (sid::stmPath) sigma)                    
                let children =
                    choices |> List.map (fun stm -> stm.GetStatementId.Value) |> Set.ofList
                                    
                let newMaxWrite =
                    let addToMapIfValueHigher (entries:Map<Var,int>) (_var:Var,version:int) : Map<Var,int> =
                        if (entries.ContainsKey _var) && (entries.Item _var >= version) then
                            entries
                        else
                            entries.Add(_var,version)
                    newSigmas |> List.collect (fun (sigma:CalculationCache) -> sigma.MaxWriteOfPredecessor |> Map.toList)
                              |> List.fold addToMapIfValueHigher Map.empty<Var,int>
                let newMaxWrite_SetForm = CalculationCache.maxWriteOfPredecessor_ToSetForm newMaxWrite
                                
                let statementInfos = sigma.StatementInfos.Value
                let mergeEntries = mergeEntriesOfVarSetMap<int>
                let read =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersion.Item child)
                             |> Seq.fold mergeEntries Map.empty<Var,Set<int>>
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersion.Item child)
                             |> Seq.fold mergeEntries Map.empty<Var,Set<int>>
                do sigma.addEntryForStatement sid read write children

                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = newMaxWrite;
                        CalculationCache.MaxWriteOfPredecessor_SetForm = newMaxWrite_SetForm
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
        let writeVersionsOfRoot = statementInfos.WriteVersion.Item pgm.Body.GetStatementId.Value
        let varVersionTuples =
            writeVersionsOfRoot |> Map.toList
                                |> List.collect (fun (var,setOfVersions) -> setOfVersions |> Set.toList |> List.map (fun version ->(var,version)))
        
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

        
    let rec replaceVarInExpr (readVersions:Map<Var,Set<int>>) (versionedVarToFreshVar:Map<Var*int,Var>) (expr:Expr) : Expr =
        match expr with
            | Expr.Literal (_) ->
                expr
            | Expr.Read (_var) ->                
                let _newVar =
                    let readVersionSetOfVar = readVersions.Item _var
                    assert (readVersionSetOfVar.Count = 1)
                    versionedVarToFreshVar.Item (_var,readVersionSetOfVar.MaximumElement)
                Expr.Read (_newVar)
            | Expr.ReadOld (_var) ->
                let _newVar =
                    let readVersionSetOfVar = readVersions.Item _var
                    assert (readVersionSetOfVar.Count = 1)
                    versionedVarToFreshVar.Item (_var,readVersionSetOfVar.MaximumElement)
                Expr.ReadOld (_newVar)
            | Expr.UExpr (expr,uop) ->
                Expr.UExpr (replaceVarInExpr readVersions versionedVarToFreshVar expr,uop)
            | Expr.BExpr (left, bop, right) ->
                Expr.BExpr (replaceVarInExpr readVersions versionedVarToFreshVar left, bop, replaceVarInExpr readVersions versionedVarToFreshVar right)

    let rec replaceVarInStm (statementInfos:StatementInfos) (versionedVarToFreshVar:Map<Var*int,Var>) (stm:Stm) : Stm =
        match stm with
            | Stm.Assert (sid,expr) ->
                let readVersions = statementInfos.ReadVersion.Item sid.Value
                Stm.Assert(sid,replaceVarInExpr readVersions versionedVarToFreshVar expr)
            | Stm.Assume (sid,expr) ->
                let readVersions = statementInfos.ReadVersion.Item sid.Value
                Stm.Assume (sid,replaceVarInExpr readVersions versionedVarToFreshVar expr)
            | Stm.Block (sid,statements) ->
                let newStmnts = statements |> List.map (replaceVarInStm statementInfos versionedVarToFreshVar)
                Stm.Block (sid,newStmnts)
            | Stm.Choice (sid,choices) ->
                let newChoices = choices |> List.map (replaceVarInStm statementInfos versionedVarToFreshVar)
                Stm.Choice (sid,newChoices)
            | Stm.Write (sid,_var,expr) ->
                let writeVersions = statementInfos.WriteVersion.Item sid.Value
                let readVersions = statementInfos.ReadVersion.Item sid.Value
                let _newVar =
                    let writeVersionSetOfVar = writeVersions.Item _var
                    assert (writeVersionSetOfVar.Count = 1)
                    versionedVarToFreshVar.Item (_var,writeVersionSetOfVar.MaximumElement)
                Stm.Write (sid,_newVar,replaceVarInExpr readVersions versionedVarToFreshVar expr)
        

        
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
            | Stm.Write (sid,_var,expr) ->
                Stm.Assume(sid,Expr.BExpr(Expr.Read(_var),BOp.Equals,expr))




    open SafetySharp.Workflow
    open VcSamWorkflow
    open VcSamModelForModification
    open SafetySharp.Models.SamHelpers
    
    let transformProgramInSsaForm1 : ModelForModificationWorkflowFunction<unit> = workflow {
        let! pgm = getVcSamModel
        let globalVars = pgm.Globals |> List.map (fun gl -> gl.Var,gl.Type)
        let localVars= pgm.Locals |> List.map (fun lo -> lo.Var,lo.Type)
        
        let statementInfos = calculateStatementInfos pgm
        let versionedVarToFreshVar = createVariablePerVariableVersion statementInfos pgm

        // replace versionedVar by fresh Var in each statement and expression
        let newBodyWithReplacedExprs = replaceVarInStm statementInfos versionedVarToFreshVar pgm.Body
        
        // add Assignments
        //todo: to add assignments, we need to introduce new statements. For that, we need new statement ids
        let newBody = newBodyWithReplacedExprs
        
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
            {
                Pgm.Body = newBody;
                Pgm.Globals = pgm.Globals; // globals stay globals
                Pgm.Locals = newLocals;
            }            
        do! setVcSamModel newPgm
    }



    //to Passive Form: 
    let transformProgramInPassiveForm1 : ModelForModificationWorkflowFunction<unit> = workflow {
        do! transformProgramInSsaForm1
        let! pgm = getVcSamModel        
        // Todo: checkEveryVariableWrittenAtMostOnce ()
        // replace all assignments by assumptions
        let newBody = replaceAssignmentByAssumption pgm.Body
        let newPgm =
            { pgm with
                Pgm.Body = newBody;
            }
        do! setVcSamModel newPgm
    }
        
    // TODO: Graph transformation

    // TODO: Local optimizations of [GCFK09], which decrease the number of copies. (Proposed in this paper)    
    // TODO: My own optimization which tries to create only as many variables as necessary for each _type_ (createVariablePerType).
    // TODO: Optimization: If a Version is never read, we can omit the assignment :-D
