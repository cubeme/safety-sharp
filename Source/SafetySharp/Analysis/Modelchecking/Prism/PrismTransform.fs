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

module internal GwamToPrism =
    
    type PrismVariables = Map<Tsam.Var,Prism.Identifier>

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

                    
    let generateInitCondition (varDecls:Tsam.GlobalVarDecl list) : Tsam.Expr =
        let generateInit (varDecl:Tsam.GlobalVarDecl) : Tsam.Expr =
            let generatePossibleValues (initialValue : Tsam.Val) : Tsam.Expr =
                let assignVar = varDecl.Var
                let assignExpr = Tsam.Expr.Literal(initialValue)
                let operator = Tsam.BOp.Equals
                Tsam.Expr.BExpr(Tsam.Expr.Read(assignVar),operator,assignExpr)
            varDecl.Init |> List.map generatePossibleValues
                         |> Tsam.createOredExpr
        varDecls |> List.map generateInit
                 |> Tsam.createAndedExpr
    
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
                (variableDeclaration,(Tsam.Traceable.Traceable(globalVarDecl.Var),variableDeclaration.Name.Name))
            gwam.Globals |> List.map transformGlobalVar
                         |> List.unzip

        // probForSure := probability = 1.0
        let probForSure = Prism.Expression.Constant(Prism.Double(1.0))

        let transformGwa (gwa:GuardWithAssignments) : Prism.Command =
            let transformedGuard = translateExpression prismIdentifiers gwa.Guard
            
            let transformAssignment (var:Tsam.Var,expr:Tsam.Expr) : (Prism.Identifier * Prism.Expression) =
                let varToWrite = prismIdentifiers.Item var
                let expr = translateExpression prismIdentifiers expr
                (varToWrite,expr)
            let transformedAssignments : (Prism.Expression * Prism.DeterministicUpdateOfVariables) =
                let probability = probForSure
                let assignment = gwa.Assignments |> Map.toList |> List.map transformAssignment
                (probability,assignment)
            let quantifiedUpdateOfVariables =
                [transformedAssignments] // we only have one element, because we currently only handle the deterministic case with probability 1.0            
            {
                Prism.Command.Action = Prism.CommandAction.NoActionLabel;
                Prism.Command.Guard = transformedGuard;
                Prism.Command.QuantifiedUpdateOfVariables = quantifiedUpdateOfVariables;
            }

        
        let moduleWithTransitions =
            let systemModuleIdentifier = {Prism.Identifier.Name="systemModule"}
            let transformedGwas = gwam.GuardsWithFinalAssignments |> List.map transformGwa
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
    open SafetySharp.Analysis.VerificationCondition
    
    let transformWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<GuardWithAssignmentModel,Prism.PrismModel,'traceableOfOrigin,VcGuardWithAssignmentModel.Traceable,Prism.Traceable,unit> = workflow {
        let! model = getState ()
        let (transformed,forwardTraceInClosure) = transformGwamToPrism model
        do! updateState transformed
        
        let intermediateTracer (oldValue:VcGuardWithAssignmentModel.Traceable) = forwardTraceInClosure.Item oldValue
        do! updateTracer intermediateTracer
    }   



