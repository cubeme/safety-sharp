// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Modelchecking.NuXmv


open SafetySharp.Modelchecking

type NuXmvProgram = SafetySharp.Modelchecking.NuXmv.NuXmvProgram
type NuXmvBasicExpression = SafetySharp.Modelchecking.NuXmv.BasicExpression
type NuXmvConstExpression = SafetySharp.Modelchecking.NuXmv.ConstExpression
type NuXmvSignSpecifier = SafetySharp.Modelchecking.NuXmv.SignSpecifier
type NuXmvRadix = SafetySharp.Modelchecking.NuXmv.Radix

type NuXmvCtlExpression = SafetySharp.Modelchecking.NuXmv.CtlExpression
type NuXmvLtlExpression = SafetySharp.Modelchecking.NuXmv.LtlExpression
type NuXmvSpecification = SafetySharp.Modelchecking.NuXmv.Specification
type NuXmvModuleTypeSpecifier = SafetySharp.Modelchecking.NuXmv.ModuleTypeSpecifier
type NuXmvModuleDeclaration = SafetySharp.Modelchecking.NuXmv.ModuleDeclaration

type MetamodelToNuXmv (configuration:MMConfiguration)  =
    let toSimplifiedMetamodel = MetamodelToSimplifiedMetamodel(configuration)

    let mainModuleIdentifier = {Identifier.Name="main"}
    
    // To transform the metamodel to NuXmv, we take an intermediate step:
    //   metamodel -> simplified metamodel -> nuxmv code
    
    // THIS IS THE MAIN FUNCTION AND ENTRY POINT
    (*member this.transformConfiguration  : NuXmvProgram =
        let varModule = this.generateFieldDeclarations
        
        let fieldInitialisations = this.generateFieldInitialisations
        
        //updates and bindings: Cover them in an endless loop
        let partitionStatements =
            //TODO: Correct semantics with bindings and correct "interleaving" of bindings and partitions
            configuration.ModelObject.Partitions |> List.collect this.generatePartitionUpdateCode 
        let codeOfMetamodel = partitionStatements
            
        let systemSequence : PrSequence = statementsToSequence (fieldInitialisations @ codeOfMetamodel)
        let systemProctype = activeProctypeWithNameAndSequence "System" systemSequence
        let systemModule = PrModule.ProcTypeModule(systemProctype)

        {
            PrSpec.Code = [varModule;systemModule];
            PrSpec.Formulas = [];
        }

     *)
    member this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier (simpleGlobalField : SimpleGlobalField) : Identifier=
        // only use, when we know that simpleGlobalField is in the partition, the method calling this function, has
        // the partition of the simpleGlobalField in mind.
        let fieldName = "f"+simpleGlobalField.field.FieldSymbol.Name
        let itemsInOrderRootToLeaf =
            simpleGlobalField.context.hierarchicalAccess |> List.rev //the order should be root::subcomponent::leafSubcomponent
        let flatSubcomponentName  = itemsInOrderRootToLeaf.Tail |> List.map (fun elem -> sprintf "c%s_" elem)
                                                                |> String.concat ""
        let flattenedNameOfField=flatSubcomponentName+fieldName;
        {Identifier.Name=flattenedNameOfField}


    member this.transformSimpleGlobalFieldToComplexIdentifier (simpleGlobalField : SimpleGlobalField) (accessFromPartition:Identifier) : ComplexIdentifier =
        // The arbitrarily complex hierarchy in the metamodel gets transformed into a two layer hierarchy: PartitionName.FlattenedNameOfField
        // The first Item in "simpleGlobalField.context.hierarchicalAccess" is the partition.
        // We want to put every partition into one module. We can associate each instanced field to its partition.
        // If the access comes from the current partition we leave out the partition in the returned partition name
        // If partitionName is empty, associate it with the main-module.
        let partitionIdentifier =
            if not (simpleGlobalField.context.rootComponentName = "") then
                {Identifier.Name=("p" + simpleGlobalField.context.rootComponentName)}
            else 
                mainModuleIdentifier
        let fieldIdentifier = this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier simpleGlobalField
        if accessFromPartition = partitionIdentifier then
            ComplexIdentifier.NameComplexIdentifier(fieldIdentifier)
        else
            let partitionContainerIdentifier = ComplexIdentifier.NameComplexIdentifier(partitionIdentifier)
            ComplexIdentifier.NestedComplexIdentifier(partitionContainerIdentifier,fieldIdentifier)
   
    member this.transformSimpleGlobalFieldToAccessExpression (simpleGlobalField : SimpleGlobalField) (accessFromPartition:Identifier) =
        let varName = this.transformSimpleGlobalFieldToComplexIdentifier simpleGlobalField accessFromPartition
        NuXmvBasicExpression.ComplexIdentifierExpression (varName)
    
    member this.generateFieldDeclarationsOfPartition (partition:Identifier) : ModuleElement =
        let fields = toSimplifiedMetamodel.getSimpleGlobalFields
        let filterInCurrentPartition (field:SimpleGlobalField) =
            field.context.rootComponentName = partition.Name //return the boolean value of the comparision. Recall: This is no assignment
        let fieldsToTransform =
            fields |> List.filter filterInCurrentPartition
        let generateDecl (field:SimpleGlobalField) : TypedIdentifier =
            let _simpleType = match field.field.FieldSymbol.Type with
                                | MMTypeSymbol.Boolean -> SimpleTypeSpecifier.BooleanTypeSpecifier
                                | MMTypeSymbol.Integer -> SimpleTypeSpecifier.IntegerTypeSpecifier
                                | MMTypeSymbol.Decimal -> SimpleTypeSpecifier.RealTypeSpecifier
            let _type = TypeSpecifier.SimpleTypeSpecifier(_simpleType)
            let _identifier = this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier field
            {
                TypedIdentifier.TypeSpecifier=_type;
                TypedIdentifier.Identifier=_identifier;
            }
        fieldsToTransform |> List.map generateDecl
                          |> ModuleElement.VarDeclaration


    (*
    member this.generateFieldInitialisations : PrStatement list =
        let fields = toSimplifiedMetamodel.getSimpleGlobalFields
        let generateInit (field:SimpleGlobalField) : PrStatement =
            let generateSequence (initialValue : obj) : PrSequence =
                let assignVarref = this.transformSimpleGlobalFieldToVarref field
                let assignExpr =
                    match initialValue with
                        | :? int as value -> PrExpression.Const(PrConst.Number(value))
                        | :? bool as value -> match value with
                                                | true  -> PrExpression.Const(PrConst.True)
                                                | false -> PrExpression.Const(PrConst.False)
                        | _ -> failwith "NotImplementedYet"
                //also possible to add a "true" as a guard to the returned sequence
                statementsToSequence [PrStatement.AssignStmnt(PrAssign.AssignExpr(assignVarref,assignExpr))]
                
            field.field.InitialValues |> List.map generateSequence
                                      |> PrOptions.Options
                                      |> PrStatement.IfStmnt
        fields |> List.map generateInit
    

    member this.generatePartitionUpdateCode (partition:MMPartitionObject) : PrStatement list=
        let partitionUpdateInSimpleStatements = toSimplifiedMetamodel.partitionUpdateInSimpleStatements partition
        let transformedSimpleStatements = partitionUpdateInSimpleStatements |> List.map this.transformSimpleStatement
        transformedSimpleStatements

    // This is currently a TODO
    member this.generatePartitionBindingCode =
        ""
    *)



    member this.transformExpressionInsideAFormula (expression:MMExpression) : NuXmvBasicExpression =
        match expression with
            | MMExpression.BooleanLiteral (value:bool) ->
                value |> NuXmvConstExpression.BooleanConstant
                      |> NuXmvBasicExpression.ConstExpression
            | MMExpression.IntegerLiteral (value:int) ->
                value |> (fun value -> new bigint(value))
                      |> NuXmvConstExpression.IntegerConstant 
                      |> NuXmvBasicExpression.ConstExpression
            | MMExpression.DecimalLiteral (value:decimal) ->
                value |> System.Decimal.ToDouble
                      |> NuXmvConstExpression.RealConstant 
                      |> NuXmvBasicExpression.ConstExpression                    
            | MMExpression.UnaryExpression (operand:MMExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformExpressionInsideAFormula operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> NuXmvBasicExpression.UnaryExpression(UnaryOperator.LogicalNot,transformedOperand)
                    | MMUnaryOperator.Minus      -> failwith "NotImplementedYet"
            | MMExpression.BinaryExpression (leftExpression:MMExpression, operator:MMBinaryOperator, rightExpression : MMExpression) ->
                let transformedLeft = this.transformExpressionInsideAFormula leftExpression
                let transformedRight = this.transformExpressionInsideAFormula rightExpression
                match operator with
                    | MMBinaryOperator.Add                -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.IntegerAddition,transformedRight)
                    | MMBinaryOperator.Subtract           -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.IntegerSubtraction,transformedRight)
                    | MMBinaryOperator.Multiply           -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.IntegerMultiplication,transformedRight)
                    | MMBinaryOperator.Divide             -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.IntegerDivision,transformedRight)
                    | MMBinaryOperator.Modulo             -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.IntegerRemainder,transformedRight)
                    | MMBinaryOperator.LogicalAnd         -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.LogicalAnd,transformedRight)
                    | MMBinaryOperator.LogicalOr          -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.LogicalOr,transformedRight)
                    | MMBinaryOperator.Equals             -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.Equality,transformedRight)
                    | MMBinaryOperator.NotEquals          -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.Inequality,transformedRight)
                    | MMBinaryOperator.LessThan           -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.LessThan,transformedRight)
                    | MMBinaryOperator.LessThanOrEqual    -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.LessEqual,transformedRight)
                    | MMBinaryOperator.GreaterThan        -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.GreaterThan,transformedRight)
                    | MMBinaryOperator.GreaterThanOrEqual -> NuXmvBasicExpression.BinaryExpression(transformedLeft,BinaryOperator.GreaterEqual,transformedRight)
            | MMExpression.FieldAccessExpression (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    failwith "Use transformExpressionInsideAFormula only for expression inside untransformed formulas and not in components"
                else
                    //called inside a formula
                    let simpleGlobalField = toSimplifiedMetamodel.resolveFieldAccessInsideAFormula componentReference.Value field
                    this.transformSimpleGlobalFieldToAccessExpression simpleGlobalField mainModuleIdentifier
                    
    member this.transformSimpleExpression (expression:MMExpression) : NuXmvBasicExpression =
        this.transformExpressionInsideAFormula (expression)
            
    (*
    member this.transformSimpleStatement (statement:SimpleStatement) : PrStatement =
        match statement with
            | SimpleStatement.GuardedCommandStatement (optionsOfGuardedCommand:(( SimpleExpression * (SimpleStatement list) ) list)) -> //Context * Guard * Statements  
                let transformOption ((guard,sequence) : (SimpleExpression * (SimpleStatement list) )) =
                    let transformedGuard = this.transformSimpleExpression guard
                    let transformedGuardStmnt = anyExprToStmnt transformedGuard
                    let transformedSequence = sequence |> List.map this.transformSimpleStatement
                    let promelaSequence = statementsToSequence (transformedGuardStmnt::transformedSequence)
                    promelaSequence
                optionsOfGuardedCommand |> List.map transformOption
                                        |> PrOptions.Options
                                        |> PrStatement.IfStmnt
            | SimpleStatement.AssignmentStatement (target:SimpleGlobalField, expression:SimpleExpression) -> //Context is only the Context of the Expression. SimpleGlobalField has its own Context (may result of a return-Statement, when context is different)
                let transformedTarget = this.transformSimpleGlobalFieldToVarref target
                let transformedExpression = this.transformSimpleExpression expression
                createAssignmentStatement transformedTarget transformedExpression

    member this.transformFormula (formula:MMFormula) : PrFormula =
        //TODO: check if LTL
        match formula with
             | MMFormula.StateFormula (stateExpression : MMExpression) ->
                PrFormula.PropositionalStateFormula(this.transformExpressionInsideAFormula stateExpression)
             | MMFormula.UnaryFormula (operand : MMFormula, operator : MMUnaryFormulaOperator) ->
                let transformedOperand = this.transformFormula operand
                match operator with
                    | MMUnaryFormulaOperator.Not      -> PrFormula.UnaryFormula(PrUnaryFormulaOperator.Not,transformedOperand)
                    | MMUnaryFormulaOperator.Next     -> failwith "UnaryTemporalOperator.Next not yet implemented in Promela. There are diverse problems with it. Read http://spinroot.com/spin/Man/ltl.html"
                    | MMUnaryFormulaOperator.Finally  -> PrFormula.UnaryFormula(PrUnaryFormulaOperator.Eventually,transformedOperand)
                    | MMUnaryFormulaOperator.Globally -> PrFormula.UnaryFormula(PrUnaryFormulaOperator.Always,transformedOperand)
                    | _ -> failwith "No CTL available"
             | MMFormula.BinaryFormula (leftFormula : MMFormula, operator : MMBinaryFormulaOperator, rightFormula : MMFormula) ->
                let transformedLeft = this.transformFormula leftFormula
                let transformedRight = this.transformFormula rightFormula
                match operator with
                    | MMBinaryFormulaOperator.And         -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.And,transformedRight)
                    | MMBinaryFormulaOperator.Or          -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Or,transformedRight)
                    | MMBinaryFormulaOperator.Implication -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Implies,transformedRight)
                    | MMBinaryFormulaOperator.Equivalence -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Equals,transformedRight)
                    | MMBinaryFormulaOperator.Until       -> PrFormula.BinaryFormula(transformedLeft,PrBinaryFormulaOperator.Until,transformedRight)
                    | _ -> failwith "No CTL available"


                    *)