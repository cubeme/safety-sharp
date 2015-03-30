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

namespace SafetySharp.Analysis.Modelchecking.NuXmv

open SafetySharp.Analysis.Modelchecking

type internal NuXmvIdentifier = SafetySharp.Analysis.Modelchecking.NuXmv.Identifier
type internal NuXmvBasicExpression = SafetySharp.Analysis.Modelchecking.NuXmv.BasicExpression
type internal NuXmvConstExpression = SafetySharp.Analysis.Modelchecking.NuXmv.ConstExpression
type internal NuXmvSignSpecifier = SafetySharp.Analysis.Modelchecking.NuXmv.SignSpecifier
type internal NuXmvRadix = SafetySharp.Analysis.Modelchecking.NuXmv.Radix

type internal NuXmvCtlExpression = SafetySharp.Analysis.Modelchecking.NuXmv.CtlExpression
type internal NuXmvLtlExpression = SafetySharp.Analysis.Modelchecking.NuXmv.LtlExpression
type internal NuXmvSpecification = SafetySharp.Analysis.Modelchecking.NuXmv.Specification
type internal NuXmvModuleTypeSpecifier = SafetySharp.Analysis.Modelchecking.NuXmv.ModuleTypeSpecifier
type internal NuXmvModuleDeclaration = SafetySharp.Analysis.Modelchecking.NuXmv.ModuleDeclaration



open SafetySharp.Analysis.Modelchecking
open SafetySharp.Models
open SafetySharp.Models.SamHelpers
open SafetySharp.Models.SamChangeIdentifier
open SafetySharp.Models.SamSimplifyBlocks
open SafetySharp.Analysis.VerificationCondition


type internal NuXmvVariables = {
    VarToNuXmvIdentifier: Map<Tsam.Var,NuXmvIdentifier>;
    VarToNuXmvComplexIdentifier: Map<Tsam.Var,NuXmv.ComplexIdentifier>;
}
    with    
        member this.generateNuXmvIdentifier (var:Tsam.Var) : (NuXmvVariables) =
            let nuXmvIdentifier = {NuXmvIdentifier.Name=var.getName}
            let nuXmvComplexIdentifier = NuXmv.ComplexIdentifier.NameComplexIdentifier(nuXmvIdentifier)
            let newState=
                { this with
                    NuXmvVariables.VarToNuXmvIdentifier = this.VarToNuXmvIdentifier.Add (var,nuXmvIdentifier)
                    NuXmvVariables.VarToNuXmvComplexIdentifier = this.VarToNuXmvComplexIdentifier.Add (var,nuXmvComplexIdentifier)
                }
            newState


module internal VcTransitionRelationToNuXmv =
    
    open TransitionSystemAsRelationExpr

    // Extension methods only valid here
    type NuXmvVariables with                
        static member initial (transitionSystem:TransitionSystem) (nameGenerator:NameGenerator) =
            // * create a nuXmv identifier for each global var
            let nuXmvKeywords: Set<string> = Set.empty<string>
            let variablesToAdd =
                let _globalVars = transitionSystem.Globals |> List.map (fun varDecl -> varDecl.Var)
                let _inputVars = transitionSystem.Ivars |> List.map (fun varDecl -> varDecl.Var)
                _globalVars@_inputVars
            let takenVariableNames = variablesToAdd |> List.map (fun varDecl -> varDecl.getName) |> Set.ofList
            let initialState =
                {
                    NuXmvVariables.VarToNuXmvIdentifier = Map.empty<Tsam.Var,NuXmvIdentifier>;
                    NuXmvVariables.VarToNuXmvComplexIdentifier = Map.empty<Tsam.Var,NuXmv.ComplexIdentifier>;
                }
                    
            let generateAndAddToList (state:NuXmvVariables) (variableToAdd:Tsam.Var): (NuXmvVariables) =
                let (newState) = state.generateNuXmvIdentifier variableToAdd
                newState
            Seq.fold generateAndAddToList (initialState) variablesToAdd
            
    let generateGlobalVarDeclarations (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : ModuleElement =
        let varDecls = transitionSystem.Globals
        let generateDecl (varDecl:Tsam.GlobalVarDecl) : TypedIdentifier =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> TypeSpecifier.SimpleTypeSpecifier(SimpleTypeSpecifier.BooleanTypeSpecifier)
                            | Sam.Type.IntType -> TypeSpecifier.SimpleTypeSpecifier(SimpleTypeSpecifier.IntegerTypeSpecifier)
                            //| SamType.Decimal -> failwith "NotImplementedYet"
            let _variable = nuXmvVariables.VarToNuXmvIdentifier.Item varDecl.Var
            {
                TypedIdentifier.Identifier = _variable ;
                TypedIdentifier.TypeSpecifier = _type ;
            }
        varDecls |> List.map generateDecl
                 |> ModuleElement.VarDeclaration
    
    let generateIvarDeclarations (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : ModuleElement =
        let ivarDecls = transitionSystem.Ivars
        let generateDecl (varDecl:Tsam.LocalVarDecl) : SimpleTypedIdentifier =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> SimpleTypeSpecifier.BooleanTypeSpecifier
                            | Sam.Type.IntType -> SimpleTypeSpecifier.IntegerTypeSpecifier
                            //| SamType.Decimal -> failwith "NotImplementedYet"
            let _variable = nuXmvVariables.VarToNuXmvIdentifier.Item varDecl.Var
            {
                SimpleTypedIdentifier.Identifier = _variable ;
                SimpleTypedIdentifier.TypeSpecifier = _type ;
            }
        ivarDecls |> List.map generateDecl
                  |> ModuleElement.IVarDeclaration
    
    let rec translateExpression (virtualNextVarToVar:Map<Tsam.Var,Tsam.Var>,nuXmvVariables:NuXmvVariables) (expr:Tsam.Expr) : NuXmvBasicExpression =
        match expr with
            | Tsam.Expr.Literal (_val) ->
                match _val with
                    | Tsam.Val.BoolVal(_val) -> NuXmvBasicExpression.ConstExpression(NuXmvConstExpression.BooleanConstant(_val))
                    | Tsam.Val.NumbVal(_val) -> NuXmvBasicExpression.ConstExpression(NuXmvConstExpression.IntegerConstant(_val))
            | Tsam.Expr.Read (_var) ->
                match virtualNextVarToVar.TryFind _var with
                    | None ->
                        NuXmvBasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item _var)
                    | Some(originalValue) ->
                        // here we have a virtual value. We want a next(originalValue) instead
                        NuXmvBasicExpression.BasicNextExpression(NuXmvBasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item originalValue))
            | Tsam.Expr.ReadOld (_var) ->            
                match virtualNextVarToVar.TryFind _var with
                    | None ->
                        NuXmvBasicExpression.ComplexIdentifierExpression(nuXmvVariables.VarToNuXmvComplexIdentifier.Item _var)
                    | Some(originalValue) ->
                        failwith "This should never occur. The source program never includes virtual var. The only parts, which use a virtual var, should use it in combination with Read()!"
            | Tsam.Expr.UExpr (expr,uop) ->
                let operator =
                    match uop with
                        | Tsam.UOp.Not -> NuXmv.UnaryOperator.LogicalNot
                NuXmvBasicExpression.UnaryExpression(operator,translateExpression (virtualNextVarToVar,nuXmvVariables) expr)
            | Tsam.Expr.BExpr (left, bop, right) ->
                let operator =
                    match bop with
                        | Tsam.BOp.Add -> NuXmv.BinaryOperator.IntegerAddition
                        | Tsam.BOp.Subtract -> NuXmv.BinaryOperator.IntegerSubtraction
                        | Tsam.BOp.Multiply -> NuXmv.BinaryOperator.IntegerMultiplication
                        | Tsam.BOp.Divide -> NuXmv.BinaryOperator.IntegerDivision
                        | Tsam.BOp.Modulo -> NuXmv.BinaryOperator.IntegerRemainder
                        | Tsam.BOp.And -> NuXmv.BinaryOperator.LogicalAnd
                        | Tsam.BOp.Or -> NuXmv.BinaryOperator.LogicalOr
                        | Tsam.BOp.Implies -> NuXmv.BinaryOperator.LogicalImplies
                        | Tsam.BOp.Equals -> NuXmv.BinaryOperator.Equality //TODO: For Binary Left and Right NuXmv.BinaryOperator.LogicalEquivalence should be better
                        | Tsam.BOp.NotEquals -> NuXmv.BinaryOperator.Inequality //TODO: For Binary Left and Right NuXmv.BinaryOperator.Xor should be better
                        | Tsam.BOp.Less -> NuXmv.BinaryOperator.LessThan
                        | Tsam.BOp.LessEqual -> NuXmv.BinaryOperator.LessEqual
                        | Tsam.BOp.Greater -> NuXmv.BinaryOperator.GreaterThan
                        | Tsam.BOp.GreaterEqual -> NuXmv.BinaryOperator.GreaterEqual
                NuXmvBasicExpression.BinaryExpression(translateExpression (virtualNextVarToVar,nuXmvVariables) left,operator,translateExpression (virtualNextVarToVar,nuXmvVariables) right)



    let generateGlobalVarInitialisations (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : ModuleElement =
        transitionSystem.Init
            |> translateExpression (transitionSystem.VirtualNextVarToVar,nuXmvVariables)
            |> ModuleElement.InitConstraint

    let generateTransRelation (transitionSystem:TransitionSystem) (nuXmvVariables:NuXmvVariables) : ModuleElement =
        ModuleElement.TransConstraint(translateExpression (transitionSystem.VirtualNextVarToVar,nuXmvVariables) transitionSystem.Trans)

    
    let transformConfiguration (transitionSystem:TransitionSystem) : NuXmvProgram =
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
                NuXmvModuleDeclaration.Identifier = {NuXmvIdentifier.Name = "main" };
                NuXmvModuleDeclaration.ModuleParameters = [];
                NuXmvModuleDeclaration.ModuleElements = [globalVarModuleElement;ivarModuleElement;globalVarInitialisations;transRelation];
            }
        
        {
            NuXmvProgram.Modules = [systemModule];
            NuXmvProgram.Specifications = [];
        }

        
    open SafetySharp.Workflow
    
    let transformTsareToNuXmvWorkflow : WorkflowFunction<TransitionSystem,NuXmvProgram,unit> = workflow {
        let! model = getState
        let transformed = transformConfiguration model
        do! updateState transformed
    }

    (*
        let reservedNames = Set.empty<string>
        do! SafetySharp.Models.TsamChangeIdentifier.changeIdentifiers reservedNames
    *)

    (*
    
    member this.transFormCtlFormula (formula:MMFormula) : CtlExpression =
        match formula with
                 | MMFormula.StateFormula (stateExpression : MMExpression) ->
                    CtlExpression.CtlSimpleExpression(this.transformExpressionInsideAFormula stateExpression)
                 | MMFormula.UnaryFormula (operand : MMFormula, operator : MMUnaryFormulaOperator) ->
                    let transformedOperand = this.transFormCtlFormula operand
                    match operator with
                        | MMUnaryFormulaOperator.Not                -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.LogicalNot,transformedOperand)
                        | MMUnaryFormulaOperator.AllPathsNext       -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.ForallNext,transformedOperand)
                        | MMUnaryFormulaOperator.AllPathsFinally    -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.ForallFinally,transformedOperand)
                        | MMUnaryFormulaOperator.AllPathsGlobally   -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.ForallGlobally,transformedOperand)
                        | MMUnaryFormulaOperator.ExistsPathNext     -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.ExistsNextState,transformedOperand)
                        | MMUnaryFormulaOperator.ExistsPathFinally  -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.ExistsFinally,transformedOperand)
                        | MMUnaryFormulaOperator.ExistsPathGlobally -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.ExistsGlobally,transformedOperand)
                        | _ -> failwith "Only CTL allowed in CTL-Mode"
                 | MMFormula.BinaryFormula (leftFormula : MMFormula, operator : MMBinaryFormulaOperator, rightFormula : MMFormula) ->
                    let transformedLeft = this.transFormCtlFormula leftFormula
                    let transformedRight = this.transFormCtlFormula rightFormula
                    match operator with
                        | MMBinaryFormulaOperator.And             -> CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalAnd,transformedRight)
                        | MMBinaryFormulaOperator.Or              -> CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalOr,transformedRight)
                        | MMBinaryFormulaOperator.Implication     -> CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalImplies,transformedRight)
                        | MMBinaryFormulaOperator.Equivalence     -> CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalEquivalence,transformedRight)
                        | MMBinaryFormulaOperator.AllPathsUntil   -> CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.ForallUntil,transformedRight)
                        | MMBinaryFormulaOperator.ExistsPathUntil -> CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.ExistsUntil,transformedRight)
                        | _ -> failwith "Only CTL allowed in CTL-Mode"

    member this.transFormLtlFormula (formula:MMFormula) : LtlExpression =
        match formula with
                 | MMFormula.StateFormula (stateExpression : MMExpression) ->
                    LtlExpression.LtlSimpleExpression(this.transformExpressionInsideAFormula stateExpression)
                 | MMFormula.UnaryFormula (operand : MMFormula, operator : MMUnaryFormulaOperator) ->
                    let transformedOperand = this.transFormLtlFormula operand
                    match operator with
                        | MMUnaryFormulaOperator.Not      -> LtlExpression.LtlUnaryExpression(LtlUnaryOperator.LogicalNot,transformedOperand)
                        | MMUnaryFormulaOperator.Next     -> LtlExpression.LtlUnaryExpression(LtlUnaryOperator.FutureNext,transformedOperand)
                        | MMUnaryFormulaOperator.Finally  -> LtlExpression.LtlUnaryExpression(LtlUnaryOperator.FutureFinally,transformedOperand)
                        | MMUnaryFormulaOperator.Globally -> LtlExpression.LtlUnaryExpression(LtlUnaryOperator.FutureGlobally,transformedOperand)
                        | _ -> failwith "Only LTL allowed in LTL-Mode"
                 | MMFormula.BinaryFormula (leftFormula : MMFormula, operator : MMBinaryFormulaOperator, rightFormula : MMFormula) ->
                    let transformedLeft = this.transFormLtlFormula leftFormula
                    let transformedRight = this.transFormLtlFormula rightFormula
                    match operator with
                        | MMBinaryFormulaOperator.And         -> LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalAnd,transformedRight)
                        | MMBinaryFormulaOperator.Or          -> LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalOr,transformedRight)
                        | MMBinaryFormulaOperator.Implication -> LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalImplies,transformedRight)
                        | MMBinaryFormulaOperator.Equivalence -> LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalEquivalence,transformedRight)
                        | MMBinaryFormulaOperator.Until       -> LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.FutureUntil,transformedRight)
                        | _ -> failwith "Only LTL allowed in LTL-Mode"

    member this.transformFormula (formula:MMFormula) : Specification =
        if formula.IsLtl() then
            this.transFormLtlFormula formula |> Specification.LtlSpecification
        else if formula.IsCtl() then
            this.transFormCtlFormula formula |> Specification.CtlSpecification
        else
            failwith "NotImplementedYet"
*)