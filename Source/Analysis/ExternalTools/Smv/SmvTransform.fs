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

// TODO: Convert vars with reserved names in NuSMV

// TODO: Overflow behavior

namespace SafetySharp.ExternalTools

open SafetySharp.Analysis.Modelchecking
open SafetySharp.Models
open SafetySharp.Models.SamHelpers
open SafetySharp.Models.SamChangeIdentifier
open SafetySharp.Models.SamSimplifyBlocks
open SafetySharp.Analysis.VerificationCondition

module internal GenericToSmv =

    type internal NuXmvVariables = {
        VarToSmvIdentifier: Map<Tsam.Var,Smv.Identifier>;
        VarToNuXmvComplexIdentifier: Map<Tsam.Var,Smv.ComplexIdentifier>;
    }
        with    
            member this.generateSmvIdentifier (var:Tsam.Var) : (NuXmvVariables) =
                let nuXmvIdentifier = {Smv.Name=var.getName}
                let nuXmvComplexIdentifier = Smv.ComplexIdentifier.NameComplexIdentifier(nuXmvIdentifier)
                let newState=
                    { this with
                        NuXmvVariables.VarToSmvIdentifier = this.VarToSmvIdentifier.Add (var,nuXmvIdentifier)
                        NuXmvVariables.VarToNuXmvComplexIdentifier = this.VarToNuXmvComplexIdentifier.Add (var,nuXmvComplexIdentifier)
                    }
                newState
                
    let rec translateExpression (virtualNextVarToVar:Map<Tsam.Var,Tsam.Var>,nuXmvVariables:NuXmvVariables) (expr:Tsam.Expr) : Smv.BasicExpression =
        match expr with
            | Tsam.Expr.Literal (_val) ->
                match _val with
                    | Tsam.Val.BoolVal(_val) -> Smv.BasicExpression.ConstExpression(Smv.BooleanConstant(_val))
                    | Tsam.Val.NumbVal(_val) -> Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(_val))
                    | Tsam.Val.RealVal _ -> failwith "No support in SMV for real values, yet."
                    | Tsam.Val.ProbVal _ -> failwith "No support in SMV for probabilities, yet."
            | Tsam.Expr.Read (_var) ->
                match virtualNextVarToVar.TryFind _var with
                    | None ->
                        Smv.BasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item _var)
                    | Some(originalValue) ->
                        // here we have a virtual value. We want a next(originalValue) instead
                        Smv.BasicExpression.BasicNextExpression(Smv.BasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item originalValue))
            | Tsam.Expr.ReadOld (_var) ->            
                match virtualNextVarToVar.TryFind _var with
                    | None ->
                        Smv.BasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item _var)
                    | Some(originalValue) ->
                        failwith "This should never occur. The source program never includes virtual var. The only parts, which use a virtual var, should use it in combination with Read()!"
            | Tsam.Expr.UExpr (expr,uop) ->
                let operator =
                    match uop with
                        | Tsam.UOp.Not -> Smv.UnaryOperator.LogicalNot
                Smv.BasicExpression.UnaryExpression(operator,translateExpression (virtualNextVarToVar,nuXmvVariables) expr)
            | Tsam.Expr.BExpr (left, bop, right) ->
                let operator =
                    match bop with
                        | Tsam.BOp.Add -> Smv.BinaryOperator.IntegerAddition
                        | Tsam.BOp.Subtract -> Smv.BinaryOperator.IntegerSubtraction
                        | Tsam.BOp.Multiply -> Smv.BinaryOperator.IntegerMultiplication
                        | Tsam.BOp.Divide -> Smv.BinaryOperator.IntegerDivision
                        | Tsam.BOp.Modulo -> Smv.BinaryOperator.IntegerRemainder
                        | Tsam.BOp.And -> Smv.BinaryOperator.LogicalAnd
                        | Tsam.BOp.Or -> Smv.BinaryOperator.LogicalOr
                        | Tsam.BOp.Implies -> Smv.BinaryOperator.LogicalImplies
                        | Tsam.BOp.Equals -> Smv.BinaryOperator.Equality //TODO: For Binary Left and Right Smv.BinaryOperator.LogicalEquivalence should be better
                        | Tsam.BOp.NotEquals -> Smv.BinaryOperator.Inequality //TODO: For Binary Left and Right Smv.BinaryOperator.Xor should be better
                        | Tsam.BOp.Less -> Smv.BinaryOperator.LessThan
                        | Tsam.BOp.LessEqual -> Smv.BinaryOperator.LessEqual
                        | Tsam.BOp.Greater -> Smv.BinaryOperator.GreaterThan
                        | Tsam.BOp.GreaterEqual -> Smv.BinaryOperator.GreaterEqual
                Smv.BasicExpression.BinaryExpression(translateExpression (virtualNextVarToVar,nuXmvVariables) left,operator,translateExpression (virtualNextVarToVar,nuXmvVariables) right)
            | Tsam.Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                let guardExpr = translateExpression (virtualNextVarToVar,nuXmvVariables) guardExpr
                let thenExpr = translateExpression (virtualNextVarToVar,nuXmvVariables) thenExpr
                let elseExpr = translateExpression (virtualNextVarToVar,nuXmvVariables) elseExpr
                Smv.BasicExpression.TenaryIfThenElseExpression(guardExpr,thenExpr,elseExpr)
                
    let noVirtualNextVarToVar = Map.empty<Tsam.Var,Tsam.Var>

    open SafetySharp.ITracing
    
    type SmvTracer<'traceableOfOrigin> = {
        SmvProgram : Smv.SmvProgram;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> Smv.Traceable;
    }
        with
            interface ITracing<Smv.SmvProgram,'traceableOfOrigin,Smv.Traceable,SmvTracer<'traceableOfOrigin>> with
                member this.getModel = this.SmvProgram
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> Smv.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> Smv.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : Smv.Traceable list = []


module internal VcTransitionRelationToNuXmv =
    open GenericToSmv
    
    open TransitionSystemAsRelationExpr

    // Extension methods only valid here
    type NuXmvVariables with                
        static member initial (transitionSystem:TransitionSystem) (nameGenerator:NameGenerator) =
            // * create a nuXmv identifier for each input and global var
            let nuXmvKeywords: Set<string> = Set.empty<string>
            let variablesToAdd =
                let _globalVars = transitionSystem.Globals |> List.map (fun varDecl -> varDecl.Var)
                let _inputVars = transitionSystem.Ivars |> List.map (fun varDecl -> varDecl.Var)
                _globalVars@_inputVars
            let takenVariableNames = variablesToAdd |> List.map (fun varDecl -> varDecl.getName) |> Set.ofList
            let initialState =
                {
                    NuXmvVariables.VarToSmvIdentifier = Map.empty<Tsam.Var,Smv.Identifier>;
                    NuXmvVariables.VarToNuXmvComplexIdentifier = Map.empty<Tsam.Var,Smv.ComplexIdentifier>;
                }
                    
            let generateAndAddToList (state:NuXmvVariables) (variableToAdd:Tsam.Var): (NuXmvVariables) =
                let (newState) = state.generateSmvIdentifier variableToAdd
                newState
            Seq.fold generateAndAddToList (initialState) variablesToAdd
            
    let generateGlobalVarDeclarations (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : Smv.ModuleElement =
        let varDecls = transitionSystem.Globals
        let generateDecl (varDecl:TransitionSystemAsRelationExpr.VarDecl) : Smv.TypedIdentifier =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> Smv.TypeSpecifier.SimpleTypeSpecifier(Smv.BooleanTypeSpecifier)
                            | Sam.Type.IntType -> Smv.TypeSpecifier.SimpleTypeSpecifier(Smv.IntegerTypeSpecifier)
                            //| SamType.Decimal -> failwith "NotImplementedYet"
                            | Sam.Type.RangedIntType (_from,_to,_) ->
                                let _from = Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(bigint _from))
                                let _to = Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(bigint _to))
                                Smv.TypeSpecifier.SimpleTypeSpecifier(Smv.IntegerRangeTypeSpecifier(_from,_to))
                            | Sam.Type.RealType -> Smv.TypeSpecifier.SimpleTypeSpecifier(Smv.RealTypeSpecifier)
                            | Sam.Type.RangedRealType _ -> failwith "No support in NuXmv for ranged real values, yet."
            let _variable = nuXmvVariables.VarToSmvIdentifier.Item varDecl.Var
            {
                Smv.TypedIdentifier.Identifier = _variable ;
                Smv.TypedIdentifier.TypeSpecifier = _type ;
            }
        varDecls |> List.map generateDecl
                 |> Smv.ModuleElement.VarDeclaration
    
    let generateIvarDeclarations (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : Smv.ModuleElement =
        let ivarDecls = transitionSystem.Ivars
        let generateDecl (varDecl:Tsam.LocalVarDecl) : Smv.SimpleTypedIdentifier =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> Smv.BooleanTypeSpecifier
                            | Sam.Type.IntType -> Smv.IntegerTypeSpecifier
                            //| SamType.Decimal -> failwith "NotImplementedYet"
                            | Sam.Type.RangedIntType (_from,_to,_) ->
                                let _from = Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(bigint _from))
                                let _to = Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(bigint _to))
                                Smv.IntegerRangeTypeSpecifier(_from,_to)
                            | Sam.Type.RealType -> Smv.RealTypeSpecifier
                            | Sam.Type.RangedRealType _ -> failwith "No support in NuXmv for ranged real values, yet."
            let _variable = nuXmvVariables.VarToSmvIdentifier.Item varDecl.Var
            {
                Smv.SimpleTypedIdentifier.Identifier = _variable ;
                Smv.SimpleTypedIdentifier.TypeSpecifier = _type ;
            }
        ivarDecls |> List.map generateDecl
                  |> Smv.ModuleElement.IVarDeclaration
    


    let generateGlobalVarInitialisations (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : Smv.ModuleElement =
        transitionSystem.Init
            |> translateExpression (transitionSystem.VirtualNextVarToVar,nuXmvVariables)
            |> Smv.ModuleElement.InitConstraint

    let generateTransRelation (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : Smv.ModuleElement =
        Smv.ModuleElement.TransConstraint(translateExpression (transitionSystem.VirtualNextVarToVar,nuXmvVariables) transitionSystem.Trans)

    
    let transformConfiguration (transitionSystem:TransitionSystem) : Smv.SmvProgram * Map<Tsam.Traceable,Smv.Traceable> =
        // create the nuXmvVariables: Keeps the association between the post value variable and the current value variable
        // (the post variable value is purely "virtual". It will be replaced by "next(currentValue)" )
        let nuXmvVariables = NuXmvVariables.initial transitionSystem SafetySharp.FreshNameGenerator.namegenerator_c_like
                                
        // declare globals variables
        let globalVarModuleElement = generateGlobalVarDeclarations transitionSystem nuXmvVariables
        
        // declare input variables
        let ivarModuleElement = generateIvarDeclarations transitionSystem nuXmvVariables
        
        // initialize globals (INIT)
        let globalVarInitialisations = generateGlobalVarInitialisations transitionSystem nuXmvVariables
        
        // program loop (TRANS)
        let transRelation  = generateTransRelation transitionSystem nuXmvVariables
        
        let systemModule =
            {
                Smv.ModuleDeclaration.Identifier = {Smv.Name = "main" };
                Smv.ModuleDeclaration.ModuleParameters = [];
                Smv.ModuleDeclaration.ModuleElements = [globalVarModuleElement;ivarModuleElement;globalVarInitialisations;transRelation];
            }
        let transformedConfiguration =
            {
                Smv.SmvProgram.Modules = [systemModule];
                Smv.SmvProgram.Specifications = [];
            }
        let tracing =
            nuXmvVariables.VarToSmvIdentifier
                |> Map.toList
                |> List.map (fun (_var,_nuxmv) -> (Tsam.Traceable.Traceable(_var),Smv.NameComplexIdentifier({Smv.Name= _nuxmv.Name}) ))
                |> Map.ofList
        (transformedConfiguration,tracing)

        
    open SafetySharp.Workflow
    
    let transformTsareToNuXmvWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<TransitionSystemTracer<'traceableOfOrigin>,SmvTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let transitionSystem = state.TransitionSystem
        let (transformedTs,forwardTraceInClosure) = transformConfiguration transitionSystem
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            forwardTraceInClosure.Item beforeTransform
        let transformed =
            {
                SmvTracer.SmvProgram= transformedTs;
                SmvTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                SmvTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }   
    

module internal StochasticProgramGraphToNuXmv =
    open GenericToSmv
    open SafetySharp.Models.Spg

    
    // Extension methods only valid here
    type NuXmvVariables with                
        static member initial (spg:StochasticProgramGraph) (nameGenerator:NameGenerator) =
            // * create a nuXmv identifier for each var
            let nuXmvKeywords: Set<string> = Set.empty<string>
            let variablesToAdd = spg.Variables |> List.map (fun varDecl -> varDecl.Var)
            let takenVariableNames = variablesToAdd |> List.map (fun varDecl -> varDecl.getName) |> Set.ofList
            let initialState =
                {
                    NuXmvVariables.VarToSmvIdentifier = Map.empty<Tsam.Var,Smv.Identifier>;
                    NuXmvVariables.VarToNuXmvComplexIdentifier = Map.empty<Tsam.Var,Smv.ComplexIdentifier>;
                }
                    
            let generateAndAddToList (state:NuXmvVariables) (variableToAdd:Tsam.Var): (NuXmvVariables) =
                let (newState) = state.generateSmvIdentifier variableToAdd
                newState
            Seq.fold generateAndAddToList (initialState) variablesToAdd
            
    let generateGlobalVarDeclarations (spg:StochasticProgramGraph) (nuXmvVariables:NuXmvVariables) : Smv.ModuleElement =
        let varDecls = spg.Variables
        let generateDecl (varDecl:Spg.VarDecl) : Smv.TypedIdentifier =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> Smv.SimpleTypeSpecifier(Smv.BooleanTypeSpecifier)
                            | Sam.Type.IntType -> Smv.SimpleTypeSpecifier(Smv.IntegerTypeSpecifier)
                            //| SamType.Decimal -> failwith "NotImplementedYet"
                            | Sam.Type.RangedIntType (_from,_to,_) ->
                                let _from = Smv.ConstExpression(Smv.IntegerConstant(bigint _from))
                                let _to = Smv.ConstExpression(Smv.IntegerConstant(bigint _to))
                                Smv.SimpleTypeSpecifier(Smv.IntegerRangeTypeSpecifier(_from,_to))
                            | Sam.Type.RealType -> Smv.SimpleTypeSpecifier(Smv.RealTypeSpecifier)
                            | Sam.Type.RangedRealType _ -> failwith "No support in NuXmv for ranged real values, yet."
            let _variable = nuXmvVariables.VarToSmvIdentifier.Item varDecl.Var
            {
                Smv.TypedIdentifier.Identifier = _variable ;
                Smv.TypedIdentifier.TypeSpecifier = _type ;
            }
        varDecls |> List.map generateDecl
                 |> Smv.ModuleElement.VarDeclaration
      

    let generateGlobalVarInitialisations (spg:StochasticProgramGraph) (nuXmvVariables:NuXmvVariables) : Smv.ModuleElement =
        let generateInitExpr (varDecl:Spg.VarDecl) : Spg.Expr =
            let generatePossibleValues (initialValue : Tsam.Val) : Spg.Expr =
                let assignVar = varDecl.Var
                let assignExpr = Spg.Expr.Literal(initialValue)
                let operator = Tsam.BOp.Equals
                Expr.BExpr(Expr.Read(assignVar),operator,assignExpr)
            varDecl.Init |> List.map generatePossibleValues
                         |> TsamHelpers.createOredExpr
        spg.Variables
            |> List.map generateInitExpr
            |> TsamHelpers.createAndedExpr
            |> translateExpression (noVirtualNextVarToVar,nuXmvVariables)
            |> Smv.ModuleElement.InitConstraint

    let generateStateVariable (spg:StochasticProgramGraph) : (Smv.BasicExpression*Map<Spg.State,Smv.BasicExpression>*Smv.ModuleElement*Smv.ModuleElement) = //StateVariable * StateToExpression-Map * Decl-ModuleElement * Init-ModuleElement
        let statecounter = ref 0
        let stateToStateExpression : Map<Spg.State,Smv.BasicExpression> =
            let createVariableForState (state:Spg.State) =
                statecounter := statecounter.Value + 1
                Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(bigint statecounter.Value))
            spg.States |> Set.toList |> List.map (fun state -> (state,createVariableForState state) ) |> Map.ofList
        let stateVariableIdentifier =
            {Smv.Name = "spgState"}
        let stateVariableExpression = Smv.BasicExpression.ComplexIdentifierExpression(Smv.NameComplexIdentifier(stateVariableIdentifier))
        let stateVarDeclElement =
            let typeSpecifier = 
                let _from = Smv.ConstExpression(Smv.IntegerConstant(bigint 1))
                let _to = Smv.ConstExpression(Smv.IntegerConstant(bigint statecounter.Value))
                Smv.TypeSpecifier.SimpleTypeSpecifier(Smv.IntegerRangeTypeSpecifier(_from,_to))
            let stateVarDecl =   
                {
                    Smv.TypedIdentifier.Identifier = stateVariableIdentifier ;
                    Smv.TypedIdentifier.TypeSpecifier = typeSpecifier ;
                }
            Smv.ModuleElement.VarDeclaration([stateVarDecl])
        let stateVarInitElement = 
            let stateEqualsInitStateExpr =
                Smv.BasicExpression.BinaryExpression(stateVariableExpression,Smv.BinaryOperator.Equality,stateToStateExpression.Item spg.InitialState)                
            Smv.ModuleElement.InitConstraint(stateEqualsInitStateExpr)
        (stateVariableExpression,stateToStateExpression,stateVarDeclElement,stateVarInitElement)


    let generateTransRelation (nuXmvVariables:NuXmvVariables)
                              (stateVariableExpr:Smv.BasicExpression, stateToExpressionMap:Map<Spg.State,Smv.BasicExpression>)
                              (transition:Spg.DeterministicTransition)
                        : Smv.BasicExpression =
        let transformAction (_var,_expr) : Smv.BasicExpression =
            let _nextVar = Smv.BasicExpression.BasicNextExpression(Smv.BasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item _var))
            let transformedExpr = translateExpression (noVirtualNextVarToVar,nuXmvVariables) _expr
            Smv.BasicExpression.BinaryExpression(_nextVar,Smv.BinaryOperator.Equality,transformedExpr)
        let transformedGuard =
            let stateGuard =
                let fromState = stateToExpressionMap.Item transition.FromState
                Smv.BasicExpression.BinaryExpression(stateVariableExpr,Smv.BinaryOperator.Equality,fromState)
            match transition.Guard with
                | None ->
                    stateGuard
                | Some (guard) ->
                    let guardExpr = translateExpression (noVirtualNextVarToVar,nuXmvVariables) guard
                    Smv.BasicExpression.BinaryExpression(stateGuard,Smv.BinaryOperator.LogicalAnd,guardExpr)
        let updateOfVariables =
            let stateAssignment =
                let nextState = Smv.BasicExpression.BasicNextExpression(stateVariableExpr)
                let toState = stateToExpressionMap.Item transition.ToState
                Smv.BasicExpression.BinaryExpression(nextState,Smv.BinaryOperator.Equality,toState)
            let transformedAction : Smv.BasicExpression =
                match transition.Action with
                    | Some (action) ->                            
                        let assignment = action |> transformAction
                        Smv.BasicExpression.BinaryExpression(stateAssignment,Smv.BinaryOperator.LogicalAnd,assignment)  // Currently Action has also only one Element + State Assignment
                    | None ->
                        stateAssignment
            transformedAction
        let transExpression =
            Smv.BasicExpression.BinaryExpression(transformedGuard,Smv.BinaryOperator.LogicalAnd,updateOfVariables)
        transExpression        

    
    let transformConfiguration (spg:StochasticProgramGraph) : Smv.SmvProgram * Map<Tsam.Traceable,Smv.Traceable> =
        // create the nuXmvVariables: Keeps the association between the post value variable and the current value variable
        // (the post variable value is purely "virtual". It will be replaced by "next(currentValue)" )
        let nuXmvVariables = NuXmvVariables.initial spg SafetySharp.FreshNameGenerator.namegenerator_c_like
                                
        // declare globals variables. 
        let globalVarModuleElement =
            //globals
            generateGlobalVarDeclarations spg nuXmvVariables
            //locals
                
        // initialize globals (INIT)
        let globalVarInitialisations = generateGlobalVarInitialisations spg nuXmvVariables
        
        let stateVariableExpression,stateToStateExpression,stateVarDeclElement,stateVarInitElement =
            generateStateVariable spg

        // program loop (TRANS)
        assert (spg.StochasticTransitions.IsEmpty)
        let transRelation  =
            spg.DeterministicTransitions |> Set.toList
                                         |> List.map (generateTransRelation nuXmvVariables (stateVariableExpression,stateToStateExpression))
                                         |> SmvAstHelpers.concatenateWithOr
                                         |> Smv.ModuleElement.TransConstraint
        
        let systemModule =
            {
                Smv.ModuleDeclaration.Identifier = {Smv.Name = "main" };
                Smv.ModuleDeclaration.ModuleParameters = [];
                Smv.ModuleDeclaration.ModuleElements = [globalVarModuleElement;globalVarInitialisations;stateVarDeclElement;stateVarInitElement;transRelation];
            }
        let transformedConfiguration =
            {
                Smv.SmvProgram.Modules = [systemModule];
                Smv.SmvProgram.Specifications = [];
            }
        let tracing =
            nuXmvVariables.VarToSmvIdentifier
                |> Map.toList
                |> List.map (fun (_var,_nuxmv) -> (Tsam.Traceable.Traceable(_var),Smv.NameComplexIdentifier({Smv.Name= _nuxmv.Name}) ))
                |> Map.ofList
        (transformedConfiguration,tracing)

        
    open SafetySharp.Workflow
    open SafetySharp.Models.SpgTracer

    let transformProgramGraphToNuXmvWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<StochasticProgramGraphTracer<'traceableOfOrigin>,SmvTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let (transformedTs,forwardTraceInClosure) = transformConfiguration (state.ProgramGraph)
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            forwardTraceInClosure.Item beforeTransform
        let transformed =
            {
                SmvTracer.SmvProgram = transformedTs;
                SmvTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                SmvTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }   



module internal ScmToNuXmv =
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmMutable
    open SafetySharp.Analysis.VerificationCondition
                
    let transformConfiguration<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> ()
                        : ExogenousWorkflowFunction<'state,GenericToSmv.SmvTracer<'traceableOfOrigin>> = workflow {
        do! SafetySharp.Models.ScmToSam.transformIscmToSam
        do! SafetySharp.Models.SamToTsam.transformSamToTsam ()

        let reservedNames = Set.empty<string>
        do! SafetySharp.Models.TsamChangeIdentifier.changeIdentifiers reservedNames
        let! tsamModel = getState ()
        let tsamModel = tsamModel.Pgm
        do printfn "%s" (SafetySharp.Models.TsamToString.exportModel tsamModel)
        do! SafetySharp.Models.TsamExplicitlyApplySemanticsOfAssignmentToRangedVariables.applySemanticsWorkflow ()

        // Way 1: Use SP-Formula. Disadvantage: Generates a lot of IVARs (I think this could be avoided, by developing an SP-Algorithm, which depends on the treeified-Form (and during traversal, every local variable is replaced by the valuation). SSA is not enough, because local variables are used to save the last values of each branch. Thus, they are needed, when branches merge again).
        //do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToPassiveForm_Original ()
        //do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformTsamToTsareWithSpWorkflow ()
        
        // Way 2: Use a) TsamToGwam or b) TsamToGwamFast
        do! SafetySharp.Models.TsamPassiveFormGCFK09.transformProgramToSsaForm_Original ()
        do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModel.transformTsamToGwaModelWorkflow () // 2a
        //do! SafetySharp.Analysis.VerificationCondition.VcGuardWithAssignmentModelFast.transformWorkflow () //2b        
        do! SafetySharp.Analysis.VerificationCondition.TransitionSystemAsRelationExpr.transformGwamToTsareWorkflow ()

        do! VcTransitionRelationToNuXmv.transformTsareToNuXmvWorkflow ()
    }

module internal ScmVeToNuXmv =
    
    open ScmVerificationElements
        
    let transformScmVal (literal:Scm.Val) : Smv.BasicExpression =
        match literal with
            | Scm.Val.BoolVal(_val) -> Smv.BasicExpression.ConstExpression(Smv.BooleanConstant(_val))
            | Scm.Val.IntVal(_val) -> Smv.BasicExpression.ConstExpression(Smv.IntegerConstant(bigint _val))
            | Scm.Val.RealVal _ -> failwith "No support in SMV for real values, yet."
            | Scm.Val.ProbVal _ -> failwith "No support in SMV for probabilities, yet."
                                            
    let transformBinaryOperator (operator:Scm.BOp) =
        match operator with
            | Scm.BOp.Add -> Smv.BinaryOperator.IntegerAddition
            | Scm.BOp.Subtract -> Smv.BinaryOperator.IntegerSubtraction
            | Scm.BOp.Multiply -> Smv.BinaryOperator.IntegerMultiplication
            | Scm.BOp.Divide -> Smv.BinaryOperator.IntegerDivision
            | Scm.BOp.Modulo -> Smv.BinaryOperator.IntegerRemainder
            | Scm.BOp.And -> Smv.BinaryOperator.LogicalAnd
            | Scm.BOp.Or -> Smv.BinaryOperator.LogicalOr
            | Scm.BOp.Equals -> Smv.BinaryOperator.Equality //TODO: For Binary Left and Right Smv.BinaryOperator.LogicalEquivalence should be better
            | Scm.BOp.NotEquals -> Smv.BinaryOperator.Inequality //TODO: For Binary Left and Right Smv.BinaryOperator.Xor should be better
            | Scm.BOp.Less -> Smv.BinaryOperator.LessThan
            | Scm.BOp.LessEqual -> Smv.BinaryOperator.LessEqual
            | Scm.BOp.Greater -> Smv.BinaryOperator.GreaterThan
            | Scm.BOp.GreaterEqual -> Smv.BinaryOperator.GreaterEqual

    let transformUnaryOperator (operator:Scm.UOp) =
        match operator with        
            | Scm.UOp.Not      -> Smv.LtlUnaryOperator.LogicalNot
            | Scm.UOp.Minus -> failwith "NotImplementedYet"               
            

    let transformScmFieldToVarref (tracer:Scm.Traceable->Smv.Traceable) (compPath:Scm.CompPath,field:Scm.Field) : Smv.ComplexIdentifier =
        let identifier = tracer (Scm.TraceableField(compPath,field))
        identifier

    let transformScmFaultToVarref (tracer:Scm.Traceable->Smv.Traceable) (compPath:Scm.CompPath,fault:Scm.Fault) : Smv.ComplexIdentifier =
        let identifier = tracer (Scm.TraceableFault(compPath,fault))
        identifier
        

    let transformBinaryLtlOperator (operator:LbOp) =
        match operator with
            | LbOp.Until -> Smv.LtlBinaryOperator.FutureUntil

    let transformUnaryLtlOperator (operator:LuOp) =
        match operator with
            | LuOp.Next       -> Smv.LtlUnaryOperator.FutureNext
            | LuOp.Eventually -> Smv.LtlUnaryOperator.FutureFinally
            | LuOp.Globally   -> Smv.LtlUnaryOperator.FutureGlobally

        
    let rec transformBasicExpression_fromLtlSubExpression (tracer:Scm.Traceable->Smv.Traceable) (expression:LtlExpr) : Smv.BasicExpression =
        // assume no temporal operators are in the expression
        match expression with
            | LtlExpr.Literal  (value) ->
                transformScmVal value
            | LtlExpr.ReadField (compPath,field) ->
                Smv.NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field))
            | LtlExpr.ReadFault (compPath,fault) ->
                Smv.NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault))
            | LtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformBasicExpression_fromLtlSubExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> Smv.BasicExpression.UnaryExpression(Smv.UnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | LtlExpr.BExpr  (left,op,right) ->
                let transformedLeft = (transformBasicExpression_fromLtlSubExpression tracer) left
                let transformedRight = (transformBasicExpression_fromLtlSubExpression tracer) right
                let transformedOperator = transformBinaryOperator op
                Smv.BasicExpression.BinaryExpression(transformedLeft,transformedOperator,transformedRight)
            | LtlExpr.LuExpr (_)
            | LtlExpr.LbExpr (_) ->
                failwith "no ltl operator should be in this sub expression"

    let rec transformLtlExpression (tracer:Scm.Traceable->Smv.Traceable) (expression:LtlExpr) : Smv.LtlExpression =
        match expression with
            | LtlExpr.Literal  (value) ->
                Smv.LtlExpression.LtlSimpleExpression(transformScmVal value)
            | LtlExpr.ReadField (compPath,field) ->
                Smv.LtlExpression.LtlSimpleExpression(Smv.NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field)))
            | LtlExpr.ReadFault (compPath,fault) ->
                Smv.LtlExpression.LtlSimpleExpression(Smv.NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault)))
            | LtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformLtlExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> Smv.LtlExpression.LtlUnaryExpression(Smv.LtlUnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | LtlExpr.BExpr  (left,op,right) ->
                match op with
                | Scm.BOp.And ->
                    let transformedLeft = (transformLtlExpression tracer) left
                    let transformedRight = (transformLtlExpression tracer) right
                    Smv.LtlExpression.LtlBinaryExpression(transformedLeft,Smv.LtlBinaryOperator.LogicalAnd,transformedRight)
                | Scm.BOp.Or ->
                    let transformedLeft = (transformLtlExpression tracer) left
                    let transformedRight = (transformLtlExpression tracer) right
                    Smv.LtlExpression.LtlBinaryExpression(transformedLeft,Smv.LtlBinaryOperator.LogicalOr,transformedRight)
                | Scm.BOp.Equals ->
                    let transformedLeft = (transformLtlExpression tracer) left
                    let transformedRight = (transformLtlExpression tracer) right
                    Smv.LtlExpression.LtlBinaryExpression(transformedLeft,Smv.LtlBinaryOperator.LogicalEquivalence,transformedRight)
                | _ ->
                    let transformedBasicExpression = transformBasicExpression_fromLtlSubExpression tracer expression
                    Smv.LtlExpression.LtlSimpleExpression(transformedBasicExpression)
            | LtlExpr.LuExpr (expr,op) ->
                let transformedOperator = transformUnaryLtlOperator op
                let transformedOperand = (transformLtlExpression tracer) expr
                Smv.LtlExpression.LtlUnaryExpression(transformedOperator,transformedOperand)
            | LtlExpr.LbExpr (left,op,right) ->
                let transformedLeft = (transformLtlExpression tracer) left
                let transformedRight = (transformLtlExpression tracer) right
                let transformedOperator = transformBinaryLtlOperator op
                Smv.LtlExpression.LtlBinaryExpression(transformedLeft,transformedOperator,transformedRight)
                

    let transformBinaryCtlOperator (operator:CbOp) =
        match operator with
            | CbOp.ExistsUntil -> Smv.CtlBinaryOperator.ExistsUntil
            | CbOp.AlwaysUntil -> Smv.CtlBinaryOperator.ForallUntil

    let transformUnaryCtlOperator (operator:CuOp) =
        match operator with
            | CuOp.ExistsNext       -> Smv.CtlUnaryOperator.ExistsNextState
            | CuOp.ExistsGlobally   -> Smv.CtlUnaryOperator.ExistsGlobally
            | CuOp.ExistsEventually -> Smv.CtlUnaryOperator.ExistsFinally
            | CuOp.AlwaysNext       -> Smv.CtlUnaryOperator.ForallNext
            | CuOp.AlwaysGlobally   -> Smv.CtlUnaryOperator.ForallGlobally
            | CuOp.AlwaysEventually -> Smv.CtlUnaryOperator.ForallFinally
                
    let rec transformBasicExpression_fromCtlSubExpression (tracer:Scm.Traceable->Smv.Traceable) (expression:CtlExpr) : Smv.BasicExpression =
        // assume no temporal operators are in the expression
        match expression with
            | CtlExpr.Literal  (value) ->
                transformScmVal value
            | CtlExpr.ReadField (compPath,field) ->
                Smv.NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field))
            | CtlExpr.ReadFault (compPath,fault) ->
                Smv.NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault))
            | CtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformBasicExpression_fromCtlSubExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> Smv.BasicExpression.UnaryExpression(Smv.UnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | CtlExpr.BExpr  (left,op,right) ->
                let transformedLeft = (transformBasicExpression_fromCtlSubExpression tracer) left
                let transformedRight = (transformBasicExpression_fromCtlSubExpression tracer) right
                let transformedOperator = transformBinaryOperator op
                Smv.BasicExpression.BinaryExpression(transformedLeft,transformedOperator,transformedRight)
            | CtlExpr.CuExpr (_)
            | CtlExpr.CbExpr (_) ->
                failwith "no ctl operator should be in this sub expression"
                
    let rec transformCtlExpression (tracer:Scm.Traceable->Smv.Traceable) (expression:CtlExpr) : Smv.CtlExpression =
        match expression with
            | CtlExpr.Literal  (value) ->
                Smv.CtlExpression.CtlSimpleExpression(transformScmVal value)
            | CtlExpr.ReadField (compPath,field) ->
                Smv.CtlExpression.CtlSimpleExpression(Smv.NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field)))
            | CtlExpr.ReadFault (compPath,fault) ->
                Smv.CtlExpression.CtlSimpleExpression(Smv.NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault)))
            | CtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformCtlExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> Smv.CtlExpression.CtlUnaryExpression(Smv.CtlUnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | CtlExpr.BExpr  (left,op,right) ->
                match op with
                | Scm.BOp.And ->
                    let transformedLeft = (transformCtlExpression tracer) left
                    let transformedRight = (transformCtlExpression tracer) right
                    Smv.CtlExpression.CtlBinaryExpression(transformedLeft,Smv.CtlBinaryOperator.LogicalAnd,transformedRight)
                | Scm.BOp.Or ->
                    let transformedLeft = (transformCtlExpression tracer) left
                    let transformedRight = (transformCtlExpression tracer) right
                    Smv.CtlExpression.CtlBinaryExpression(transformedLeft,Smv.CtlBinaryOperator.LogicalOr,transformedRight)
                | Scm.BOp.Equals ->
                    let transformedLeft = (transformCtlExpression tracer) left
                    let transformedRight = (transformCtlExpression tracer) right
                    Smv.CtlExpression.CtlBinaryExpression(transformedLeft,Smv.CtlBinaryOperator.LogicalEquivalence,transformedRight)
                | _ ->
                    let transformedBasicExpression = transformBasicExpression_fromCtlSubExpression tracer expression
                    Smv.CtlExpression.CtlSimpleExpression(transformedBasicExpression)
            | CtlExpr.CuExpr (expr,op) ->
                let transformedOperator = transformUnaryCtlOperator op
                let transformedOperand = (transformCtlExpression tracer) expr
                Smv.CtlExpression.CtlUnaryExpression(transformedOperator,transformedOperand)
            | CtlExpr.CbExpr (left,op,right) ->
                let transformedLeft = (transformCtlExpression tracer) left
                let transformedRight = (transformCtlExpression tracer) right
                let transformedOperator = transformBinaryCtlOperator op
                Smv.CtlExpression.CtlBinaryExpression(transformedLeft,transformedOperator,transformedRight)