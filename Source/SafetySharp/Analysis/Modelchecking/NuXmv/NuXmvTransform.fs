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
type internal NuXmvTraceable = SafetySharp.Analysis.Modelchecking.NuXmv.Traceable

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
                            | Sam.Type.RangedIntType (_from,_to,_) ->
                                let _from = BasicExpression.ConstExpression(ConstExpression.IntegerConstant(bigint _from))
                                let _to = BasicExpression.ConstExpression(ConstExpression.IntegerConstant(bigint _to))
                                TypeSpecifier.SimpleTypeSpecifier(SimpleTypeSpecifier.IntegerRangeTypeSpecifier(_from,_to))
                            | Sam.Type.RealType -> TypeSpecifier.SimpleTypeSpecifier(SimpleTypeSpecifier.RealTypeSpecifier)
                            | Sam.Type.RangedRealType _ -> failwith "No support in NuXmv for ranged real values, yet."
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
                            | Sam.Type.RangedIntType (_from,_to,_) ->
                                let _from = BasicExpression.ConstExpression(ConstExpression.IntegerConstant(bigint _from))
                                let _to = BasicExpression.ConstExpression(ConstExpression.IntegerConstant(bigint _to))
                                SimpleTypeSpecifier.IntegerRangeTypeSpecifier(_from,_to)
                            | Sam.Type.RealType -> SimpleTypeSpecifier.RealTypeSpecifier
                            | Sam.Type.RangedRealType _ -> failwith "No support in NuXmv for ranged real values, yet."
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
                    | Tsam.Val.RealVal _ -> failwith "No support in SMV for real values, yet."
                    | Tsam.Val.ProbVal _ -> failwith "No support in SMV for probabilities, yet."
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

    
    let transformConfiguration (transitionSystem:TransitionSystem) : NuXmvProgram * Map<Tsam.Traceable,NuXmvTraceable> =
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
        let transformedConfiguration =
            {
                NuXmvProgram.Modules = [systemModule];
                NuXmvProgram.Specifications = [];
            }
        let tracing =
            nuXmvVariables.VarToNuXmvIdentifier
                |> Map.toList
                |> List.map (fun (_var,_nuxmv) -> (Tsam.Traceable.Traceable(_var),ComplexIdentifier.NameComplexIdentifier({Identifier.Name= _nuxmv.Name}) ))
                |> Map.ofList
        (transformedConfiguration,tracing)

        
    open SafetySharp.Workflow
    open SafetySharp.ITracing
    
    type NuXmvTracer<'traceableOfOrigin> = {
        NuXmvProgram : NuXmvProgram;
        TraceablesOfOrigin : 'traceableOfOrigin list;
        ForwardTracer : 'traceableOfOrigin -> NuXmv.Traceable;
    }
        with
            interface ITracing<NuXmvProgram,'traceableOfOrigin,NuXmv.Traceable,NuXmvTracer<'traceableOfOrigin>> with
                member this.getModel = this.NuXmvProgram
                member this.getTraceablesOfOrigin : 'traceableOfOrigin list = this.TraceablesOfOrigin
                member this.setTraceablesOfOrigin (traceableOfOrigin:('traceableOfOrigin list)) = {this with TraceablesOfOrigin=traceableOfOrigin}
                member this.getForwardTracer : ('traceableOfOrigin -> NuXmv.Traceable) = this.ForwardTracer
                member this.setForwardTracer (forwardTracer:('traceableOfOrigin -> NuXmv.Traceable)) = {this with ForwardTracer=forwardTracer}
                member this.getTraceables : NuXmv.Traceable list = []
    
    let transformTsareToNuXmvWorkflow<'traceableOfOrigin> ()
            : ExogenousWorkflowFunction<TransitionSystemTracer<'traceableOfOrigin>,NuXmvTracer<'traceableOfOrigin>> = workflow {
        let! state = getState ()
        let transitionSystem = state.TransitionSystem
        let (transformedTs,forwardTraceInClosure) = transformConfiguration transitionSystem
        let tracer (oldValue:'traceableOfOrigin) =
            let beforeTransform = state.ForwardTracer oldValue
            forwardTraceInClosure.Item beforeTransform
        let transformed =
            {
                NuXmvTracer.NuXmvProgram = transformedTs;
                NuXmvTracer.TraceablesOfOrigin = state.TraceablesOfOrigin;
                NuXmvTracer.ForwardTracer = tracer;
            }
        do! updateState transformed
    }   
    
module internal ScmToNuXmv =

    open SafetySharp.Workflow
    open SafetySharp.Models.ScmMutable
    open SafetySharp.Analysis.VerificationCondition
                
    let transformConfiguration<'traceableOfOrigin,'state when 'state :> IScmMutable<'traceableOfOrigin,'state>> ()
                        : ExogenousWorkflowFunction<'state,VcTransitionRelationToNuXmv.NuXmvTracer<'traceableOfOrigin>> = workflow {
        do! SafetySharp.Models.ScmToSam.transformIscmToSam
        do! SafetySharp.Models.SamToTsam.transformSamToTsam ()
        let reservedNames = Set.empty<string>
        do! SafetySharp.Models.TsamChangeIdentifier.changeIdentifiers reservedNames
        let! tsamModel = getState ()
        let tsamModel = tsamModel.Pgm
        do printfn "%s" (SafetySharp.Models.TsamToString.exportModel tsamModel)

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
        
    let transformScmVal (literal:Scm.Val) : NuXmvBasicExpression =
        match literal with
            | Scm.Val.BoolVal(_val) -> NuXmvBasicExpression.ConstExpression(NuXmvConstExpression.BooleanConstant(_val))
            | Scm.Val.IntVal(_val) -> NuXmvBasicExpression.ConstExpression(NuXmvConstExpression.IntegerConstant(bigint _val))
            | Scm.Val.RealVal _ -> failwith "No support in SMV for real values, yet."
            | Scm.Val.ProbVal _ -> failwith "No support in SMV for probabilities, yet."
                                            
    let transformBinaryOperator (operator:Scm.BOp) =
        match operator with
            | Scm.BOp.Add -> NuXmv.BinaryOperator.IntegerAddition
            | Scm.BOp.Subtract -> NuXmv.BinaryOperator.IntegerSubtraction
            | Scm.BOp.Multiply -> NuXmv.BinaryOperator.IntegerMultiplication
            | Scm.BOp.Divide -> NuXmv.BinaryOperator.IntegerDivision
            | Scm.BOp.Modulo -> NuXmv.BinaryOperator.IntegerRemainder
            | Scm.BOp.And -> NuXmv.BinaryOperator.LogicalAnd
            | Scm.BOp.Or -> NuXmv.BinaryOperator.LogicalOr
            | Scm.BOp.Equals -> NuXmv.BinaryOperator.Equality //TODO: For Binary Left and Right NuXmv.BinaryOperator.LogicalEquivalence should be better
            | Scm.BOp.NotEquals -> NuXmv.BinaryOperator.Inequality //TODO: For Binary Left and Right NuXmv.BinaryOperator.Xor should be better
            | Scm.BOp.Less -> NuXmv.BinaryOperator.LessThan
            | Scm.BOp.LessEqual -> NuXmv.BinaryOperator.LessEqual
            | Scm.BOp.Greater -> NuXmv.BinaryOperator.GreaterThan
            | Scm.BOp.GreaterEqual -> NuXmv.BinaryOperator.GreaterEqual

    let transformUnaryOperator (operator:Scm.UOp) =
        match operator with        
            | Scm.UOp.Not      -> LtlUnaryOperator.LogicalNot
            | Scm.UOp.Minus -> failwith "NotImplementedYet"               
            

    let transformScmFieldToVarref (tracer:Scm.Traceable->Traceable) (compPath:Scm.CompPath,field:Scm.Field) : ComplexIdentifier =
        let identifier = tracer (Scm.TraceableField(compPath,field))
        identifier

    let transformScmFaultToVarref (tracer:Scm.Traceable->Traceable) (compPath:Scm.CompPath,fault:Scm.Fault) : ComplexIdentifier =
        let identifier = tracer (Scm.TraceableFault(compPath,fault))
        identifier
        

    let transformBinaryLtlOperator (operator:LbOp) =
        match operator with
            | LbOp.Until -> LtlBinaryOperator.FutureUntil

    let transformUnaryLtlOperator (operator:LuOp) =
        match operator with
            | LuOp.Next       -> LtlUnaryOperator.FutureNext
            | LuOp.Eventually -> LtlUnaryOperator.FutureFinally
            | LuOp.Globally   -> LtlUnaryOperator.FutureGlobally

        
    let rec transformBasicExpression_fromLtlSubExpression (tracer:Scm.Traceable->Traceable) (expression:LtlExpr) : BasicExpression =
        // assume no temporal operators are in the expression
        match expression with
            | LtlExpr.Literal  (value) ->
                transformScmVal value
            | LtlExpr.ReadField (compPath,field) ->
                NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field))
            | LtlExpr.ReadFault (compPath,fault) ->
                NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault))
            | LtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformBasicExpression_fromLtlSubExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> BasicExpression.UnaryExpression(UnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | LtlExpr.BExpr  (left,op,right) ->
                let transformedLeft = (transformBasicExpression_fromLtlSubExpression tracer) left
                let transformedRight = (transformBasicExpression_fromLtlSubExpression tracer) right
                let transformedOperator = transformBinaryOperator op
                BasicExpression.BinaryExpression(transformedLeft,transformedOperator,transformedRight)
            | LtlExpr.LuExpr (_)
            | LtlExpr.LbExpr (_) ->
                failwith "no ltl operator should be in this sub expression"

    let rec transformLtlExpression (tracer:Scm.Traceable->Traceable) (expression:LtlExpr) : LtlExpression =
        match expression with
            | LtlExpr.Literal  (value) ->
                LtlExpression.LtlSimpleExpression(transformScmVal value)
            | LtlExpr.ReadField (compPath,field) ->
                LtlExpression.LtlSimpleExpression(NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field)))
            | LtlExpr.ReadFault (compPath,fault) ->
                LtlExpression.LtlSimpleExpression(NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault)))
            | LtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformLtlExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> LtlExpression.LtlUnaryExpression(LtlUnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | LtlExpr.BExpr  (left,op,right) ->
                match op with
                | Scm.BOp.And ->
                    let transformedLeft = (transformLtlExpression tracer) left
                    let transformedRight = (transformLtlExpression tracer) right
                    LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalAnd,transformedRight)
                | Scm.BOp.Or ->
                    let transformedLeft = (transformLtlExpression tracer) left
                    let transformedRight = (transformLtlExpression tracer) right
                    LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalOr,transformedRight)
                | Scm.BOp.Equals ->
                    let transformedLeft = (transformLtlExpression tracer) left
                    let transformedRight = (transformLtlExpression tracer) right
                    LtlExpression.LtlBinaryExpression(transformedLeft,LtlBinaryOperator.LogicalEquivalence,transformedRight)
                | _ ->
                    let transformedBasicExpression = transformBasicExpression_fromLtlSubExpression tracer expression
                    LtlExpression.LtlSimpleExpression(transformedBasicExpression)
            | LtlExpr.LuExpr (expr,op) ->
                let transformedOperator = transformUnaryLtlOperator op
                let transformedOperand = (transformLtlExpression tracer) expr
                LtlExpression.LtlUnaryExpression(transformedOperator,transformedOperand)
            | LtlExpr.LbExpr (left,op,right) ->
                let transformedLeft = (transformLtlExpression tracer) left
                let transformedRight = (transformLtlExpression tracer) right
                let transformedOperator = transformBinaryLtlOperator op
                LtlExpression.LtlBinaryExpression(transformedLeft,transformedOperator,transformedRight)
                

    let transformBinaryCtlOperator (operator:CbOp) =
        match operator with
            | CbOp.ExistsUntil -> CtlBinaryOperator.ExistsUntil
            | CbOp.AlwaysUntil -> CtlBinaryOperator.ForallUntil

    let transformUnaryCtlOperator (operator:CuOp) =
        match operator with
            | CuOp.ExistsNext       -> CtlUnaryOperator.ExistsNextState
            | CuOp.ExistsGlobally   -> CtlUnaryOperator.ExistsGlobally
            | CuOp.ExistsEventually -> CtlUnaryOperator.ExistsFinally
            | CuOp.AlwaysNext       -> CtlUnaryOperator.ForallNext
            | CuOp.AlwaysGlobally   -> CtlUnaryOperator.ForallGlobally
            | CuOp.AlwaysEventually -> CtlUnaryOperator.ForallFinally
                
    let rec transformBasicExpression_fromCtlSubExpression (tracer:Scm.Traceable->Traceable) (expression:CtlExpr) : BasicExpression =
        // assume no temporal operators are in the expression
        match expression with
            | CtlExpr.Literal  (value) ->
                transformScmVal value
            | CtlExpr.ReadField (compPath,field) ->
                NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field))
            | CtlExpr.ReadFault (compPath,fault) ->
                NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault))
            | CtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformBasicExpression_fromCtlSubExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> BasicExpression.UnaryExpression(UnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | CtlExpr.BExpr  (left,op,right) ->
                let transformedLeft = (transformBasicExpression_fromCtlSubExpression tracer) left
                let transformedRight = (transformBasicExpression_fromCtlSubExpression tracer) right
                let transformedOperator = transformBinaryOperator op
                BasicExpression.BinaryExpression(transformedLeft,transformedOperator,transformedRight)
            | CtlExpr.CuExpr (_)
            | CtlExpr.CbExpr (_) ->
                failwith "no ctl operator should be in this sub expression"
                
    let rec transformCtlExpression (tracer:Scm.Traceable->Traceable) (expression:CtlExpr) : CtlExpression =
        match expression with
            | CtlExpr.Literal  (value) ->
                CtlExpression.CtlSimpleExpression(transformScmVal value)
            | CtlExpr.ReadField (compPath,field) ->
                CtlExpression.CtlSimpleExpression(NextExpression.ComplexIdentifierExpression ( transformScmFieldToVarref tracer (compPath,field)))
            | CtlExpr.ReadFault (compPath,fault) ->
                CtlExpression.CtlSimpleExpression(NextExpression.ComplexIdentifierExpression ( transformScmFaultToVarref tracer (compPath,fault)))
            | CtlExpr.UExpr (expr,op) ->
                let transformedOperand = (transformCtlExpression tracer) expr
                match op with
                    | Scm.UOp.Not -> CtlExpression.CtlUnaryExpression(CtlUnaryOperator.LogicalNot,transformedOperand)
                    | _ -> failwith  "NotImplementedYet"
            | CtlExpr.BExpr  (left,op,right) ->
                match op with
                | Scm.BOp.And ->
                    let transformedLeft = (transformCtlExpression tracer) left
                    let transformedRight = (transformCtlExpression tracer) right
                    CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalAnd,transformedRight)
                | Scm.BOp.Or ->
                    let transformedLeft = (transformCtlExpression tracer) left
                    let transformedRight = (transformCtlExpression tracer) right
                    CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalOr,transformedRight)
                | Scm.BOp.Equals ->
                    let transformedLeft = (transformCtlExpression tracer) left
                    let transformedRight = (transformCtlExpression tracer) right
                    CtlExpression.CtlBinaryExpression(transformedLeft,CtlBinaryOperator.LogicalEquivalence,transformedRight)
                | _ ->
                    let transformedBasicExpression = transformBasicExpression_fromCtlSubExpression tracer expression
                    CtlExpression.CtlSimpleExpression(transformedBasicExpression)
            | CtlExpr.CuExpr (expr,op) ->
                let transformedOperator = transformUnaryCtlOperator op
                let transformedOperand = (transformCtlExpression tracer) expr
                CtlExpression.CtlUnaryExpression(transformedOperator,transformedOperand)
            | CtlExpr.CbExpr (left,op,right) ->
                let transformedLeft = (transformCtlExpression tracer) left
                let transformedRight = (transformCtlExpression tracer) right
                let transformedOperator = transformBinaryCtlOperator op
                CtlExpression.CtlBinaryExpression(transformedLeft,transformedOperator,transformedRight)