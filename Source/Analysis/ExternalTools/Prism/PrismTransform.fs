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

// We use MDPs. If we could assume that every choice is non-deterministic, we could also use DTMCs

namespace SafetySharp.Analysis.Modelchecking.Prism

open SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel
open SafetySharp.Models
open SafetySharp.Models.SamHelpers
open SafetySharp.Analysis.Modelchecking

module internal GenericToPrism =
    type PrismVariables = Map<Tsam.Var,Prism.Identifier>
    
    // probForSure := probability = 1.0
    let probForSure = Prism.Expression.Constant(Prism.Double(1.0))

    

    let createPrismIdentifiers (vars:Tsam.Var list) : PrismVariables =
        let initialMap = Map.empty<Tsam.Var,Prism.Identifier>
        let nameGenerator = SafetySharp.FreshNameGenerator.namegenerator_c_like
        let takenNames = ("systemModule"::Prism.Identifier.reserved) |> Set.ofList
        let addVar (currentEntries:Map<Tsam.Var,Prism.Identifier>,takenNames:Set<string>) (varToAdd:Tsam.Var) : (Map<Tsam.Var,Prism.Identifier>*Set<string>) =
            let newNameAsString = nameGenerator takenNames (varToAdd.getName)
            let newTakenNames = takenNames.Add newNameAsString
            let newVarMap=currentEntries.Add (varToAdd,{Prism.Identifier.Name=newNameAsString})
            newVarMap,newTakenNames
        let varMap,takenNames = vars |> List.fold addVar (initialMap,takenNames)
        varMap
    
    let translateLiteral (_val : Tsam.Val ) : Prism.Expression =
        match _val with
            | Tsam.Val.BoolVal(_val) -> Prism.Constant(Prism.Boolean(_val))
            | Tsam.Val.NumbVal(_val) -> Prism.Constant(Prism.Integer(int _val))
            | Tsam.Val.RealVal(_val) -> Prism.Constant(Prism.Double(_val))
            | Tsam.Val.ProbVal(_val) -> Prism.Constant(Prism.Double(_val))

    let rec translateExpression (prismVariables:PrismVariables) (expr:Tsam.Expr) : Prism.Expression =
        match expr with
            | Tsam.Expr.Literal (_val) ->
                translateLiteral _val
            | Tsam.Expr.Read (_var) ->
                Prism.Variable(prismVariables.Item _var)
            | Tsam.Expr.ReadOld (_var) ->            
                Prism.Variable(prismVariables.Item _var)
            | Tsam.Expr.UExpr (expr,uop) ->
                let uexpr =
                    match uop with
                        | Tsam.UOp.Not -> Prism.UnaryNot
                uexpr (translateExpression prismVariables expr)
            | Tsam.Expr.BExpr (left, bop, right) ->
                let left = translateExpression prismVariables left
                let right = translateExpression prismVariables right
                match bop with
                    | Tsam.BOp.Add ->          Prism.BinaryAddition(left,right)
                    | Tsam.BOp.Subtract ->     Prism.BinarySubstraction(left,right)
                    | Tsam.BOp.Multiply ->     Prism.BinaryMultiplication(left,right)
                    | Tsam.BOp.Divide ->       Prism.BinaryDivision(left,right)
                    | Tsam.BOp.Modulo ->       failwith "NotImplementedYet"
                    | Tsam.BOp.And ->          Prism.BinaryConjunction(left,right)
                    | Tsam.BOp.Or ->           Prism.BinaryDisjunction(left,right)
                    | Tsam.BOp.Implies ->      Prism.BinaryImplication(left,right)
                    | Tsam.BOp.Equals ->       Prism.BinaryEquals(left,right)
                    | Tsam.BOp.NotEquals ->    Prism.BinaryNotEquals(left,right)
                    | Tsam.BOp.Less ->         Prism.BinaryLessThan(left,right)
                    | Tsam.BOp.LessEqual ->    Prism.BinaryLessEqual(left,right)
                    | Tsam.BOp.Greater ->      Prism.BinaryGreaterThan(left,right)
                    | Tsam.BOp.GreaterEqual -> Prism.BinaryGreaterEqual(left,right)
            | Tsam.Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                let guardExpr = translateExpression prismVariables guardExpr
                let thenExpr = translateExpression prismVariables thenExpr
                let elseExpr = translateExpression prismVariables elseExpr
                Prism.TenaryIfThenElse(guardExpr,thenExpr,elseExpr)

                    
    let generateInitCondition (varDecls:Tsam.GlobalVarDecl list) : Tsam.Expr =
        let generateInit (varDecl:Tsam.GlobalVarDecl) : Tsam.Expr =
            let generatePossibleValues (initialValue : Tsam.Val) : Tsam.Expr =
                let assignVar = varDecl.Var
                let assignExpr = Tsam.Expr.Literal(initialValue)
                let operator = Tsam.BOp.Equals
                Tsam.Expr.BExpr(Tsam.Expr.Read(assignVar),operator,assignExpr)
            varDecl.Init |> List.map generatePossibleValues
                         |> TsamHelpers.createOredExpr
        varDecls |> List.map generateInit
                 |> TsamHelpers.createAndedExpr
    
    let transformTsamTypeToPrismType (_type:Tsam.Type) : Prism.VariableDeclarationType =
        match _type with
            | Tsam.Type.BoolType -> Prism.VariableDeclarationType.Bool
            | Tsam.Type.IntType -> Prism.VariableDeclarationType.Int
            | Tsam.Type.RangedIntType (_from,_to,_) ->
                let _from = Prism.Expression.Constant(Constant.Integer(_from))
                let _to = Prism.Expression.Constant(Constant.Integer(_to))
                Prism.VariableDeclarationType.IntRange(_from,_to)
            | Tsam.Type.RealType -> failwith "No support in Prism for real values, yet."
            | Tsam.Type.RangedRealType _ -> failwith "No support in Prism for ranged real values, yet."

            
    open SafetySharp.Workflow
    open SafetySharp.ITracing

    type PrismModelTracer<'traceableOfOrigin> = {
        PrismModel : Prism.PrismModel;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Prism.Traceable;
    }
        with
            interface ITracing<Prism.PrismModel,'traceableOfOrigin,Prism.Traceable,PrismModelTracer<'traceableOfOrigin>> with
                member this.getModel = this.PrismModel
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Prism.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Prism.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : Prism.Traceable list = []


module internal GwamToPrism =
    open GenericToPrism
    
    let transformGwamToPrism (gwam:GuardWithAssignmentModel) : (Prism.PrismModel*Map<Traceable,Prism.Traceable>) =
        let allInitsDeterministic = gwam.Globals |> List.forall (fun gl -> gl.Init.Length = 1 )

        let prismIdentifiers = gwam.Globals |> List.map (fun gl -> gl.Var) |> createPrismIdentifiers
        
        let initModule =
            if allInitsDeterministic then
                None
            else
                gwam.Globals |> generateInitCondition  |> (translateExpression prismIdentifiers) |> Some
        
        let (globalVariables,forwardTrace) =
            let transformGlobalVar (globalVarDecl:Tsam.GlobalVarDecl) : (Prism.VariableDeclaration*(Traceable*Prism.Traceable)) =
                let variableDeclaration =
                    {
                        VariableDeclaration.Name = prismIdentifiers.Item (globalVarDecl.Var);
                        VariableDeclaration.Type = transformTsamTypeToPrismType (globalVarDecl.Type);
                        VariableDeclaration.InitialValue =
                            if allInitsDeterministic then
                                Some(translateLiteral (globalVarDecl.Init.Head) )
                            else
                                None
                    }
                (variableDeclaration,(Tsam.Traceable.Traceable(globalVarDecl.Var),Prism.Traceable(variableDeclaration.Name.Name)))
            gwam.Globals |> List.map transformGlobalVar
                         |> List.unzip
                         
        let transformAssignments (assignments:Assignments) : Prism.Command =        
            let transformAssignment (var:Tsam.Var,expr:Tsam.Expr) : (Prism.Identifier * Prism.Expression) =
                let varToWrite = prismIdentifiers.Item var
                let expr = translateExpression prismIdentifiers expr
                (varToWrite,expr)

            let transformedGuard,quantifiedUpdateOfVariables =
                match assignments with            
                    | Assignments.Deterministic (guard:Expr, assignments:FinalVariableAssignments) ->
                        let transformedGuard = translateExpression prismIdentifiers guard
                        let transformedAssignments : (Prism.Expression * Prism.DeterministicUpdateOfVariables) list =
                            let probability = probForSure
                            let assignment = assignments.Assignments |> Map.toList |> List.map transformAssignment
                            [(probability,assignment)]  // we only have one element, because we handle the deterministic case with probability 1.0
                        (transformedGuard,transformedAssignments)
                    | Assignments.Stochastic (guard:Expr, assignments:(StochasticAssignment list)) ->
                        let transformedGuard = translateExpression prismIdentifiers guard
                        let transformAssignment (assignment:StochasticAssignment) : (Prism.Expression * Prism.DeterministicUpdateOfVariables) =
                            let probability = translateExpression prismIdentifiers (assignment.Probability)
                            let assignment = assignment.Assignments.Assignments |> Map.toList |> List.map transformAssignment
                            (probability,assignment)
                        let transformedAssignments = assignments |> List.map transformAssignment
                        (transformedGuard,transformedAssignments)
            {
                Prism.Command.Action = Prism.CommandAction.NoActionLabel;
                Prism.Command.Guard = transformedGuard;
                Prism.Command.QuantifiedUpdateOfVariables = quantifiedUpdateOfVariables;
            }

        
        let moduleWithTransitions =
            let systemModuleIdentifier = {Prism.Identifier.Name="systemModule"}
            let transformedGwas = gwam.Assignments |> List.map transformAssignments
            Prism.Module(systemModuleIdentifier,[],transformedGwas)
        
        let prismModel = 
            {
                Prism.PrismModel.ModelType = Prism.ModelType.MDP;
                Prism.PrismModel.Constants = [];
                Prism.PrismModel.InitModule = initModule; //Chapter Multiple Initial States e.g. "x+y=1"
                Prism.PrismModel.GlobalVariables = globalVariables;
                Prism.PrismModel.Modules = [moduleWithTransitions];
                Prism.PrismModel.Formulas = [];
                Prism.PrismModel.Labels = [];
                Prism.PrismModel.Rewards = [];
                Prism.PrismModel.ParallelComposition = None;
            }
        let forwardTrace = forwardTrace |> Map.ofList
        (prismModel,forwardTrace)


        
    open SafetySharp.Workflow

    let transformWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<GuardWithAssignmentModelTracer<'traceableOfOrigin>,PrismModelTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let model = state.GuardWithAssignmentModel
        let (transformedModel,forwardTraceInClosure) = transformGwamToPrism model
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            let intermediateTracer (oldValue:Sam.Traceable) =
                match oldValue with
                    | Sam.TraceableRemoved(reason) -> Prism.TraceableRemoved(reason)
                    | _ -> forwardTraceInClosure.Item oldValue

            intermediateTracer beforeTransform
        let transformed =
            {
                PrismModelTracer.PrismModel = transformedModel;
                PrismModelTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                PrismModelTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }

    
module internal StochasticProgramGraphToPrism =
    open GenericToPrism
    open SafetySharp.Models.Spg

    let transformSpgToPrism (spg:StochasticProgramGraph) : (Prism.PrismModel*Map<Traceable,Prism.Traceable>) =
        
        let allInitsDeterministic = spg.Variables |> List.forall (fun gl -> gl.Init.Length = 1 )

        let prismIdentifiers = spg.Variables |> List.map (fun gl -> gl.Var) |> createPrismIdentifiers
        
        let initModule =
            if allInitsDeterministic then
                None
            else
                spg.Variables |> generateInitCondition  |> (translateExpression prismIdentifiers) |> Some
        
        
        let stateToNumber : Map<Spg.State,Prism.Constant> =
            let statecounter = ref 0
            let createVariableForState (state:Spg.State) =
                statecounter := statecounter.Value + 1
                Prism.Integer(statecounter.Value)
            spg.States |> Set.toList |> List.map (fun state -> (state,createVariableForState state) ) |> Map.ofList
        let stateVariableIdentifier =
            {Prism.Identifier.Name = "spgState"}
        let stateVariable =
            {
                VariableDeclaration.Name = stateVariableIdentifier
                VariableDeclaration.Type =
                    let _from = Prism.Expression.Constant(Prism.Integer(1))
                    let _to= Prism.Expression.Constant(Prism.Integer(stateToNumber.Count))
                    Prism.VariableDeclarationType.IntRange(_from,_to)
                VariableDeclaration.InitialValue = 
                    Some(Prism.Expression.Constant(stateToNumber.Item spg.InitialState)  )
            }

        let (globalVariables,forwardTrace) =
            let transformVarDecl (varDecl:VarDecl) : (Prism.VariableDeclaration*(Traceable*Prism.Traceable)) =
                let variableDeclaration =
                    {
                        VariableDeclaration.Name = prismIdentifiers.Item (varDecl.Var);
                        VariableDeclaration.Type = transformTsamTypeToPrismType (varDecl.Type);
                        VariableDeclaration.InitialValue =
                            if allInitsDeterministic then
                                Some(translateLiteral (varDecl.Init.Head) )
                            else
                                None
                    }
                (variableDeclaration,(Tsam.Traceable.Traceable(varDecl.Var),Prism.Traceable (variableDeclaration.Name.Name)))
            let globalVariables,forwardTrace =
                spg.Variables |> List.map transformVarDecl
                              |> List.unzip
            let globalVariablesWithStateVariable = stateVariable::globalVariables
            (globalVariablesWithStateVariable,forwardTrace)

        
        let transformAction (var:Tsam.Var,expr:Tsam.Expr) : (Prism.Identifier * Prism.Expression) =
            let varToWrite = prismIdentifiers.Item var
            let expr = translateExpression prismIdentifiers expr
            (varToWrite,expr)

        let transformDeterministicTransition (transition:DeterministicTransition) : Prism.Command =
            let transformedGuard =
                let stateGuard = Expression.BinaryEquals(Expression.Variable(stateVariableIdentifier),Prism.Expression.Constant(stateToNumber.Item transition.FromState))
                match transition.Guard with
                    | None ->
                        stateGuard
                    | Some (guard) ->
                        let guardExpr = translateExpression prismIdentifiers guard
                        Expression.BinaryConjunction(stateGuard,guardExpr)                        
            let quantifiedUpdateOfVariables =
                let stateAssignment = (stateVariableIdentifier,Prism.Expression.Constant(stateToNumber.Item transition.ToState))
                let transformedAction : (Prism.Expression * Prism.DeterministicUpdateOfVariables) list =
                    let probability = probForSure
                    match transition.Action with
                        | Some (action) ->                            
                            let assignment = action |> transformAction
                            [(probability,[stateAssignment;assignment])]  // we only have one element, because we handle the deterministic case with probability 1.0. Currently Action has also only one Element + State Assignment
                        | None ->
                            [(probability,[stateAssignment])]
                transformedAction
            {
                Prism.Command.Action = Prism.CommandAction.NoActionLabel;
                Prism.Command.Guard = transformedGuard;
                Prism.Command.QuantifiedUpdateOfVariables = quantifiedUpdateOfVariables;
            }

        let transformStochasticTransition (transition:StochasticTransition) : Prism.Command =
            let transformedGuard =
                let stateGuard = Expression.BinaryEquals(Expression.Variable(stateVariableIdentifier),Prism.Expression.Constant(stateToNumber.Item transition.FromState))
                match transition.Guard with
                    | None ->
                        stateGuard
                    | Some (guard) ->
                        let guardExpr = translateExpression prismIdentifiers guard
                        Expression.BinaryConjunction(stateGuard,guardExpr)         
            let quantifiedUpdateOfVariables =
                let transformOption (option:StochasticOption) : (Prism.Expression * Prism.DeterministicUpdateOfVariables) =
                    let stateAssignment = (stateVariableIdentifier,Prism.Expression.Constant(stateToNumber.Item option.ToState))
                    let probability = translateExpression prismIdentifiers (option.Probability)
                    match option.Action with
                        | Some (action) ->                            
                            let assignment = action |> transformAction
                            (probability,[stateAssignment;assignment])
                        | None ->
                            (probability,[stateAssignment])
                let transformedOptions = transition.Options |> List.map transformOption
                transformedOptions
            {
                Prism.Command.Action = Prism.CommandAction.NoActionLabel;
                Prism.Command.Guard = transformedGuard;
                Prism.Command.QuantifiedUpdateOfVariables = quantifiedUpdateOfVariables;
            }
        
        let moduleWithTransitions =
            let systemModuleIdentifier = {Prism.Identifier.Name="systemModule"}
            let transformedTransitions =
                let deterministic = spg.DeterministicTransitions |> Set.toList |> List.map transformDeterministicTransition
                let stochastic = spg.StochasticTransitions |> Set.toList |> List.map transformStochasticTransition
                //TODO: Add transitions from EndOfLoopStates to InitialState
                deterministic @ stochastic
            Prism.Module(systemModuleIdentifier,[],transformedTransitions)
        
        let prismModel = 
            {
                Prism.PrismModel.ModelType = Prism.ModelType.MDP;
                Prism.PrismModel.Constants = [];
                Prism.PrismModel.InitModule = initModule; //Chapter Multiple Initial States e.g. "x+y=1"
                Prism.PrismModel.GlobalVariables = globalVariables;
                Prism.PrismModel.Modules = [moduleWithTransitions];
                Prism.PrismModel.Formulas = [];
                Prism.PrismModel.Labels = [];
                Prism.PrismModel.Rewards = [];
                Prism.PrismModel.ParallelComposition = None;
            }
        let forwardTrace = forwardTrace |> Map.ofList
        (prismModel,forwardTrace)
        
    open SafetySharp.Workflow
    open SafetySharp.Models.SpgTracer

    let transformWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<StochasticProgramGraphTracer<'traceableOfOrigin>,PrismModelTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let model = state.ProgramGraph
        let (transformedModel,forwardTraceInClosure) = transformSpgToPrism model
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            let intermediateTracer (oldValue:Sam.Traceable) =
                match oldValue with
                    | Sam.TraceableRemoved(reason) -> Prism.TraceableRemoved(reason)
                    | _ -> forwardTraceInClosure.Item oldValue

            intermediateTracer beforeTransform
        let transformed =
            {
                PrismModelTracer.PrismModel = transformedModel;
                PrismModelTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                PrismModelTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }