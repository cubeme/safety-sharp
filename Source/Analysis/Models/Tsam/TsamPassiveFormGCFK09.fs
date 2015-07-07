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

// Modification of the original algorithm: Add currently unwritten statements

// TODO: Switch ReadVersion to actually read versions and WriteVersion to actually written versions



module internal TsamPassiveFormGCFK09 =
    open SafetySharp.Models.SamHelpers
    open Tsam
    open TsamHelpers
    
    type StatementInfos =
        {
            ReadVersions : Map<StatementId,Set<Element*int>> 
            WriteVersions : Map<StatementId,Set<Element*int>>
            FirstRead : Map<StatementId,Map<Element,int>>
            MaxLastWrite : Map<StatementId,Map<Element,int>>
            Children : Map<StatementId,Set<StatementId>>
        }
            with
                static member initial =
                    {
                        StatementInfos.ReadVersions = Map.empty<StatementId,Set<Element*int>>;
                        StatementInfos.WriteVersions = Map.empty<StatementId,Set<Element*int>>;
                        StatementInfos.FirstRead = Map.empty<StatementId,Map<Element,int>>
                        StatementInfos.MaxLastWrite = Map.empty<StatementId,Map<Element,int>>
                        StatementInfos.Children = Map.empty<StatementId,Set<StatementId>>;
                    }
                    
    
    type CalculationCache =
        {
            StatementInfos : StatementInfos ref;
            MaxWriteOfPredecessor : Map<Element,int> // Element to MaxWriteOfPredecessorOfElement
            //NodesToRefresh : Set<int>
        }
            with
                static member initial (pgm:Pgm) =
                    let globalVars:Set<Var> = pgm.Globals |> List.map (fun g -> g.Var) |> Set.ofList
                    let localVars:Set<Var> = pgm.Locals |> List.map (fun l -> l.Var) |> Set.ofList
                    let maxWriteOfPredecessor =
                        // global fields have already been written to (in earlier steps or been initialized). Set the counter there to 1
                        let globalVarVersions = globalVars |> Set.fold (fun (acc:Map<Element,int>) (elem:Var) -> acc.Add(Element.GlobalVar elem,1)) Map.empty<Element,int>;
                        // Set counter of local variables to 0. Value 0 means default value of type.
                        let globalAndLocalVarVersions = localVars |> Set.fold (fun (acc:Map<Element,int>) (elem:Var) -> acc.Add(Element.LocalVar elem,0)) globalVarVersions;
                        globalAndLocalVarVersions
                        

                    {
                        CalculationCache.StatementInfos = ref StatementInfos.initial
                        CalculationCache.MaxWriteOfPredecessor = maxWriteOfPredecessor;
                    }
                
                member this.addEntryForStatement (sid:StatementId) (readVersion:Set<Element*int>)
                                                                   (writeVersion:Set<Element*int>)
                                                                   (firstRead:Map<Element,int>)
                                                                   (maxLastWrite:Map<Element,int>)
                                                                   (children:Set<StatementId>) : unit =
                    let statementInfos = this.StatementInfos.Value
                    this.StatementInfos :=
                        { statementInfos with                            
                            StatementInfos.ReadVersions = statementInfos.ReadVersions.Add(sid,readVersion)
                            StatementInfos.WriteVersions = statementInfos.WriteVersions.Add(sid,writeVersion)
                            StatementInfos.FirstRead = statementInfos.FirstRead.Add(sid,firstRead)
                            StatementInfos.MaxLastWrite = statementInfos.MaxLastWrite.Add(sid,maxLastWrite)
                            StatementInfos.Children = statementInfos.Children.Add(sid,children)
                        }
    
    let rec readsOfExpression (currentVersions:Map<Element,int>) (acc:Set<Element*int>) (expr:Expr) : Set<Element*int> =
        match expr with
            | Expr.Literal _ ->
                acc
            | Expr.Read (element) ->                
                acc.Add( (element,currentVersions.Item element) )
            | Expr.ReadOld (element) ->
                acc.Add( (element,1) ) //initial version of a global field is 1
            | Expr.UExpr (expr,uop) ->
                readsOfExpression currentVersions acc expr
            | Expr.BExpr (left, bop, right) ->
                let readsOfLeft = readsOfExpression currentVersions acc left
                let readsOfRight = readsOfExpression currentVersions acc right
                Set.union readsOfLeft readsOfRight
            | Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->                
                let readsOfGuard = readsOfExpression currentVersions acc guardExpr
                let readsOfThen = readsOfExpression currentVersions acc thenExpr
                let readsOfElse = readsOfExpression currentVersions acc elseExpr
                Set.unionMany [readsOfGuard;readsOfThen;readsOfElse]

    let rec calculateStatementInfosAcc (stmPath:StatementId list) (sigma:CalculationCache) (stm:Stm) : CalculationCache =
        // This function is not side-effect-free. It is only intended as Worker for calculateStatementInfos, which provides
        // an immutable interface
        // afterwards sigma.StatementInfos contains all necessary information
        match stm with
            | Stm.Assert (sid,expr) ->
                let read = readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Element*int> expr
                let write = Set.empty<Element*int>
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite = sigma.MaxWriteOfPredecessor
                let children = (Set.empty<StatementId>)
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children
                sigma
            | Stm.Assume (sid,expr) ->
                let read = readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Element*int> expr
                let write = Set.empty<Element*int>
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite = sigma.MaxWriteOfPredecessor
                let children = (Set.empty<StatementId>)
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children
                sigma
            | Stm.Write (sid,variable,expression) ->
                let read = readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Element*int> expression
                let writeVersion =
                    let oldVersion = sigma.MaxWriteOfPredecessor.Item variable
                    oldVersion + 1
                let write = Set.empty<Element*int>.Add( (variable,writeVersion) )
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite =
                    sigma.MaxWriteOfPredecessor.Add(variable,writeVersion)                    
                let children = (Set.empty<StatementId>)
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children                
                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma
            | Stm.Block (sid,statements) ->
                let newSigmaAfterStatements =
                    List.fold (calculateStatementInfosAcc (sid::stmPath)) sigma statements
                let children =
                    statements |> List.map (fun stm -> stm.GetStatementId) |> Set.ofList
                
                let statementInfos = newSigmaAfterStatements.StatementInfos.Value
                let read =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Element*int>
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Element*int>
                let firstRead = sigma.MaxWriteOfPredecessor
                let maxLastWrite = newSigmaAfterStatements.MaxWriteOfPredecessor
                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children

                let newSigma =
                    { newSigmaAfterStatements with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma
            | Stm.Choice (sid,choices) ->  
                let readsOfGuards =
                    choices |> List.map (fun (choiceGuard,_) ->
                                            if choiceGuard.IsSome then 
                                                readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Element*int> choiceGuard.Value
                                            else
                                                Set.empty<Element*int>
                                        )
                            |> Set.unionMany

                let newSigmas =
                    choices |> List.map (fun (_,choiceStm) -> calculateStatementInfosAcc (sid::stmPath) sigma choiceStm)
                let children =
                    choices |> List.map (fun (_,choiceStm) -> choiceStm.GetStatementId) |> Set.ofList
                                                                    
                let statementInfos = sigma.StatementInfos.Value
                let read =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Element*int>
                             |> Set.union readsOfGuards
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Element*int>
                let firstRead = sigma.MaxWriteOfPredecessor                
                let maxLastWrite =
                    let addToMapIfValueHigher (entries:Map<Element,int>) (_var:Element,version:int) : Map<Element,int> =
                        if (entries.ContainsKey _var) && (entries.Item _var >= version) then
                            entries
                        else
                            entries.Add(_var,version)
                    newSigmas |> List.collect (fun (sigma:CalculationCache) -> sigma.MaxWriteOfPredecessor |> Map.toList)
                              |> List.fold addToMapIfValueHigher Map.empty<Element,int>

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
                    stochasticChoices |> List.map (fun (stochasticChoiceExpr,_) -> readsOfExpression sigma.MaxWriteOfPredecessor Set.empty<Element*int> stochasticChoiceExpr)
                                      |> Set.unionMany

                let newSigmas =
                    stochasticChoices |> List.map (fun (_,stochaticChoiceStm) -> calculateStatementInfosAcc (sid::stmPath) sigma stochaticChoiceStm)
                let children =
                    stochasticChoices |> List.map (fun (_,stochaticChoiceStm) -> stochaticChoiceStm.GetStatementId) |> Set.ofList
                                                                    
                let statementInfos = sigma.StatementInfos.Value
                let read =
                    // be careful: This node also reads stuff in its expression
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.ReadVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Element*int>
                             |> Set.union readsOfProbabilistic
                let write =
                    children |> Set.toSeq
                             |> Seq.map (fun child -> statementInfos.WriteVersions.Item child)
                             |> Seq.fold Set.union Set.empty<Element*int>
                let firstRead = sigma.MaxWriteOfPredecessor                
                let maxLastWrite =
                    let addToMapIfValueHigher (entries:Map<Element,int>) (_var:Element,version:int) : Map<Element,int> =
                        if (entries.ContainsKey _var) && (entries.Item _var >= version) then
                            entries
                        else
                            entries.Add(_var,version)
                    newSigmas |> List.collect (fun (sigma:CalculationCache) -> sigma.MaxWriteOfPredecessor |> Map.toList)
                              |> List.fold addToMapIfValueHigher Map.empty<Element,int>

                do sigma.addEntryForStatement sid read write firstRead maxLastWrite children

                let newSigma =
                    { sigma with
                        CalculationCache.MaxWriteOfPredecessor = maxLastWrite;
                    }
                newSigma

    let calculateStatementInfos (pgm:Pgm) : StatementInfos =
        // the returned StatementInfos is immutable        
        let cacheWithGlobals = CalculationCache.initial pgm

        let resultingCache = calculateStatementInfosAcc [] cacheWithGlobals pgm.Body
        resultingCache.StatementInfos.Value
    
    
    let createLocalVarElementPerElementVersion (statementInfos:StatementInfos) (pgm:Pgm) : Map<Element*int,Element> =
        // get written versions of the root node
        let writeVersionsOfRoot = statementInfos.WriteVersions.Item pgm.Body.GetStatementId
        let readVersionsOfRoot = statementInfos.ReadVersions.Item pgm.Body.GetStatementId
        let initialVersions =
            // Otherwise, if the initial version of a variable is never read, it does not appear in the set varVersionTuple.
            // But it might be necessary for the missing statements. (See smokeTest6.sam)
            pgm.Globals |> List.map (fun gl -> (Element.GlobalVar gl.Var,1) ) |> Set.ofList
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
        
        let createNewElement (based_on:Element) (version:int) : Element =
            let newName =
                match based_on with
                    | Element.GlobalVar (var)
                    | Element.LocalVar (var) -> createNewName var version
            Element.LocalVar (Var.Var(newName))
        
        let createFreshVarsForNewElementVersions (element:Element,version:int) =
            if version = 1 || version = 0 then
                // keep, no need for first version (or the default value) to create a new variable. Version 0 is never used. We could also filter it out.
                ((element,version),element)
            else
                let freshElement = createNewElement element version
                ((element,version),freshElement)
        
        let newMap = varVersionTuples |> List.map createFreshVarsForNewElementVersions |> Map.ofList
        newMap
    
        
    let rec replaceVarInExpr (readVersions:Map<Element,int>) (versionedElementToFreshElement:Map<Element*int,Element>) (elementToType:Map<Element,Type>) (expr:Expr) : Expr =
        match expr with
            | Expr.Literal (_) ->
                expr
            | Expr.Read (_var) ->
                let readVersionOfVar = readVersions.Item _var                
                if readVersionOfVar = 0 then
                    // version 0 means default value
                    Expr.Literal( (elementToType.Item _var).getDefaultValue )
                else
                    // if version >= 1 we use the new fresh name created by createFreshVarsForNewVariableVersions
                    let _newVar =
                        versionedElementToFreshElement.Item (_var,readVersionOfVar)
                    Expr.Read (_newVar)
            | Expr.ReadOld (_var) ->
                expr //old variables keep their value. TODO: Write Smoketest. Assumption: Only works for fields
            | Expr.UExpr (expr,uop) ->
                Expr.UExpr (replaceVarInExpr readVersions versionedElementToFreshElement elementToType expr,uop)
            | Expr.BExpr (left, bop, right) ->
                Expr.BExpr (replaceVarInExpr readVersions versionedElementToFreshElement elementToType left, bop, replaceVarInExpr readVersions versionedElementToFreshElement elementToType right)                
            | Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                Expr.IfThenElseExpr (replaceVarInExpr readVersions versionedElementToFreshElement elementToType guardExpr, replaceVarInExpr readVersions versionedElementToFreshElement elementToType thenExpr, replaceVarInExpr readVersions versionedElementToFreshElement elementToType elseExpr)                

    let rec replaceVarInStm (statementInfos:StatementInfos) (versionedElementToFreshElement:Map<Element*int,Element>) (elementToType:Map<Element,Type>) (stm:Stm) : Stm =
        match stm with
            | Stm.Assert (sid,expr) ->
                let readVersions = statementInfos.FirstRead.Item sid
                Stm.Assert(sid,replaceVarInExpr readVersions versionedElementToFreshElement elementToType expr)
            | Stm.Assume (sid,expr) ->
                let readVersions = statementInfos.FirstRead.Item sid
                Stm.Assume (sid,replaceVarInExpr readVersions versionedElementToFreshElement elementToType expr)
            | Stm.Block (sid,statements) ->
                let newStmnts = statements |> List.map (replaceVarInStm statementInfos versionedElementToFreshElement elementToType)
                Stm.Block (sid,newStmnts)
            | Stm.Choice (sid,choices) ->
                let readVersions = statementInfos.FirstRead.Item sid
                let rewriteChoice (choiceExpr:Expr option,choiceStm) =
                    let newStochasticExpr =
                        if choiceExpr.IsSome then
                            Some(replaceVarInExpr readVersions versionedElementToFreshElement elementToType choiceExpr.Value)
                        else
                            None
                    let newStochasticStm = replaceVarInStm statementInfos versionedElementToFreshElement elementToType choiceStm
                    (newStochasticExpr,newStochasticStm)
                let newChoices = choices |> List.map rewriteChoice
                Stm.Choice (sid,newChoices)
            | Stm.Stochastic (sid,stochasticChoices) ->
                let readVersions = statementInfos.FirstRead.Item sid
                let rewriteChoice (stochasticExpr,stochasticStm) =
                    let newStochasticExpr = replaceVarInExpr readVersions versionedElementToFreshElement elementToType stochasticExpr
                    let newStochasticStm = replaceVarInStm statementInfos versionedElementToFreshElement elementToType stochasticStm
                    (newStochasticExpr,newStochasticStm)
                let newChoices = stochasticChoices |> List.map rewriteChoice
                Stm.Stochastic (sid,newChoices)
            | Stm.Write (sid,_var,expr) ->
                let writeVersions = statementInfos.MaxLastWrite.Item sid
                let readVersions = statementInfos.FirstRead.Item sid
                let _newVar =
                    let writeVersionOfVar = writeVersions.Item _var
                    versionedElementToFreshElement.Item (_var,writeVersionOfVar)
                Stm.Write (sid,_newVar,replaceVarInExpr readVersions versionedElementToFreshElement elementToType expr)
        
    let rec addMissingAssignmentsBeforeMerges (statementInfos:StatementInfos) (uniqueStatementIdGenerator : unit -> StatementId) (versionedElementToFreshElement:Map<Element*int,Element>) (elementToType:Map<Element,Type>) (stm:Stm) : Stm =
        match stm with
            | Stm.Assert (sid,expr) ->
                stm
            | Stm.Assume (sid,expr) ->
                stm
            | Stm.Block (sid,statements) ->
                let newStmnts = statements |> List.map (addMissingAssignmentsBeforeMerges statementInfos uniqueStatementIdGenerator versionedElementToFreshElement elementToType)
                Stm.Block (sid,newStmnts)
            | Stm.Choice (sid,choices) ->
                let recursiveAddMissing (choiceGuard,choiceStm) =
                    let newChoiceStm = addMissingAssignmentsBeforeMerges statementInfos uniqueStatementIdGenerator versionedElementToFreshElement elementToType choiceStm
                    (choiceGuard,newChoiceStm)
                let newChoices = choices |> List.map recursiveAddMissing
                let readOfNextNode = statementInfos.MaxLastWrite.Item sid
                //Note: maxLastWrite of this statement is firstRead of next Statement. Thus we still check the formula int the paper.
                let addMissingAssignmentsToBranch (branch:Stm) : Stm =
                    let maxLastWriteOfBranch = statementInfos.MaxLastWrite.Item branch.GetStatementId
                    let missingStatementsOfBranch =
                        let createAssignment (element:Element,nextReadVersion:int,lastWriteVersionOfBranch:int) =
                            let freshStatementId = uniqueStatementIdGenerator ()
                            let assignTo = versionedElementToFreshElement.Item (element,nextReadVersion)
                            let assignExpr =
                                if lastWriteVersionOfBranch = 0 then
                                    // version 0 means default value
                                    Expr.Literal( (elementToType.Item element).getDefaultValue )
                                else
                                    // if version >= 1 we use the new fresh name created by createFreshVarsForNewVariableVersions
                                    Expr.Read(versionedElementToFreshElement.Item (element,lastWriteVersionOfBranch))
                            Stm.Write(freshStatementId,assignTo,assignExpr)                            
                        readOfNextNode |> Map.toList
                                       |> List.map (fun (_var,nextReadVersion ) -> (_var,nextReadVersion, maxLastWriteOfBranch.Item _var ) )
                                       |> List.filter (fun (_var,nextReadVersion , lastWriteVersionOfBranch) -> nextReadVersion<>lastWriteVersionOfBranch )
                                       |> List.map createAssignment
                    branch.appendStatements uniqueStatementIdGenerator missingStatementsOfBranch
                // check each new branch
                let newChoices =
                    newChoices |> List.map (fun (choiceGuard,choiceStm) -> (choiceGuard,addMissingAssignmentsToBranch choiceStm))
                Stm.Choice (sid,newChoices)
            | Stm.Stochastic (sid,stochasticChoices) ->
                // adapted just code of Stm.Choice
                let recursiveAddMissing (stochasticExpr,stochasticStm) =
                    let newStochasticStm = addMissingAssignmentsBeforeMerges statementInfos uniqueStatementIdGenerator versionedElementToFreshElement elementToType stochasticStm
                    (stochasticExpr,newStochasticStm)
                let newChoices = stochasticChoices |> List.map recursiveAddMissing                
                let readOfNextNode = statementInfos.MaxLastWrite.Item sid
                //Note: maxLastWrite of this statement is firstRead of next Statement. Thus we still check the formula int the paper.
                let addMissingAssignmentsToBranch (branch:Stm) : Stm =
                    let maxLastWriteOfBranch = statementInfos.MaxLastWrite.Item branch.GetStatementId
                    let missingStatementsOfBranch =
                        let createAssignment (element:Element,nextReadVersion:int,lastWriteVersionOfBranch:int) =
                            let freshStatementId = uniqueStatementIdGenerator ()
                            let assignTo = versionedElementToFreshElement.Item (element,nextReadVersion)
                            let assignExpr =
                                if lastWriteVersionOfBranch = 0 then
                                    // version 0 means default value
                                    Expr.Literal( (elementToType.Item element).getDefaultValue )
                                else
                                    // if version >= 1 we use the new fresh name created by createFreshVarsForNewVariableVersions
                                    Expr.Read(versionedElementToFreshElement.Item (element,lastWriteVersionOfBranch))
                            Stm.Write(freshStatementId,assignTo,assignExpr)                            
                        readOfNextNode |> Map.toList
                                       |> List.map (fun (_var,nextReadVersion ) -> (_var,nextReadVersion, maxLastWriteOfBranch.Item _var ) )
                                       |> List.filter (fun (_var,nextReadVersion , lastWriteVersionOfBranch) -> nextReadVersion<>lastWriteVersionOfBranch )
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
                let newChoices = choices |> List.map (fun (choiceGuard,choiceStm) -> (choiceGuard,replaceAssignmentByAssumption choiceStm))
                Stm.Choice (sid,newChoices)
            | Stm.Stochastic (sid,stochasticChoices) ->
                let newChoices = stochasticChoices |> List.map (fun (stochasticExpr,stochasticStm) -> (stochasticExpr,replaceAssignmentByAssumption stochasticStm))
                Stm.Stochastic (sid,newChoices)
            | Stm.Write (sid,_var,expr) ->
                Stm.Assume(sid,Expr.BExpr(Expr.Read(_var),BOp.Equals,expr))

    open SafetySharp.Workflow
    open SafetySharp.Models.SamHelpers
    
    let transformProgramToSsaForm_Original<'traceableOfOrigin>
            () : EndogenousWorkflowFunction<TsamTracer.TsamTracer<'traceableOfOrigin>> = workflow {
        do! TsamTracer.prependKeepValueAssignments ()
        let! state = getState ()
        let pgm = state.Pgm
        let globalVars = pgm.Globals |> List.map (fun gl -> gl.Var,gl.Type)
        let localVars = pgm.Locals |> List.map (fun lo -> lo.Var,lo.Type)
        
        let statementInfos = calculateStatementInfos pgm
        
        let elementToTypeOld = TsamHelpers.createElementToType (pgm.Globals,pgm.Locals)

        let versionedElementToFreshElement = createLocalVarElementPerElementVersion statementInfos pgm
        // replace versionedVar by fresh Var in each statement and expression
        let newBodyWithReplacedExprs = replaceVarInStm statementInfos versionedElementToFreshElement elementToTypeOld pgm.Body
        // Add Assignments. To add assignments, we need to introduce new statements. For that, we need new statement ids
        let newBodyWithoutMissingAssignments = addMissingAssignmentsBeforeMerges statementInfos pgm.UniqueStatementIdGenerator versionedElementToFreshElement elementToTypeOld newBodyWithReplacedExprs
        // statementInfos is now outdated
        
        let mappingToNextGlobal : Map<Var,Var> =
            //NextGlobal maps to each global variable var_i the variable var_j, which contains the value of var_i, after Body was executed. var_i can be var_j (substitution)
            let maxLastWriteOfRoot = statementInfos.MaxLastWrite.Item pgm.Body.GetStatementId
            let globalVarSet = pgm.Globals |> List.map (fun gl -> gl.Var) |> Set.ofList
            let nextVarOfElement (element:Element,nextVarVersion:int) : Var * Var =
                let oldVar =
                    match element with
                        | Element.GlobalVar (_var) -> _var
                        | _ -> failwith "this function should only be applied on global vars"
                let newVar =
                    let newElement = versionedElementToFreshElement.Item(element,nextVarVersion)                    
                    match element with
                        | Element.GlobalVar (_var)
                        | Element.LocalVar (_var) -> _var
                (oldVar,newVar)

            maxLastWriteOfRoot |> Map.toSeq
                               |> Seq.filter (fun (element,_) -> match element with | Element.GlobalVar _ -> true | _ -> false ) //only use global vars and not local vars
                               |> Seq.map nextVarOfElement
                               |> Map.ofSeq
        // statementInfos is now useless
                

        let newPgm =
            let createLocalVarDecl (element:Element,_type) =
                match element with
                    | Element.LocalVar(_var) -> LocalVarDecl.createLocalVarDecl _var _type
                    | _ -> failwith "this function should be called, after global variables have been filtered out"                
            let oldGlobalsAsSet = pgm.Globals |> List.map (fun gl -> gl.Var) |> Set.ofList
            let newLocals =
                let newVersions =
                    versionedElementToFreshElement |> Map.toList
                                                   |> List.filter (fun ((_var1,version),_var2) -> match _var2 with | Element.LocalVar _ -> true | _ -> false)
                                                   |> List.map (fun ((_var1,version),_var2) -> createLocalVarDecl (_var2,elementToTypeOld.Item _var1) ) 
                (newVersions @ pgm.Locals)
            { pgm with
                Pgm.Body = newBodyWithoutMissingAssignments;
                Pgm.Globals = pgm.Globals; // globals stay globals
                Pgm.Locals = newLocals;
                Pgm.ElementToType = TsamHelpers.createElementToType (pgm.Globals,newLocals);
                Pgm.CodeForm = CodeForm.SingleAssignments;
                Pgm.NextGlobal = mappingToNextGlobal;
            }            
        let newState = {state with Pgm=newPgm}
        do! updateState newState
    }



    //to Passive Form: 
    let transformProgramToPassiveForm_Original<'traceableOfOrigin>
            () : EndogenousWorkflowFunction<TsamTracer.TsamTracer<'traceableOfOrigin>> = workflow {
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
