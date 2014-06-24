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
        if not simpleGlobalField.hasContext then
            failwith "SimpleGlobalFields in this function must belong to a partition"
        let flatSubcomponentName (context:Context) : string =
            let itemsInOrderRootToLeaf =
                context.hierarchicalAccess |> List.rev //the order should be root::subcomponent::leafSubcomponent
            itemsInOrderRootToLeaf.Tail |> List.map (fun elem -> sprintf "c%s_" elem)
                                        |> String.concat ""
        match simpleGlobalField with
            | SimpleGlobalField.FieldLinkedToMetamodel(_,context:Context, field:MMFieldObject) ->
                let fieldName = "f"+field.FieldSymbol.Name
                let flattenedNameOfField = (flatSubcomponentName context) + fieldName;
                {Identifier.Name=flattenedNameOfField}


    member this.transformSimpleGlobalFieldToComplexIdentifier (simpleGlobalField : SimpleGlobalField) (accessFromPartition:Identifier) : ComplexIdentifier =
        if simpleGlobalField.hasContext then
            // The arbitrarily complex hierarchy in the metamodel gets transformed into a two layer hierarchy: PartitionName.FlattenedNameOfField
            // The first Item in "simpleGlobalField.context.hierarchicalAccess" is the partition.
            // We want to put every partition into one module. We can associate each instanced field to its partition.
            // If the access comes from the current partition we leave out the partition in the returned partition name
            // If partitionName is empty, associate it with the main-module.
            let context = simpleGlobalField.getContext
            let partitionIdentifier =
                if not (context.rootComponentName = "") then
                    {Identifier.Name=("p" + context.rootComponentName)}
                else 
                    mainModuleIdentifier
            let fieldIdentifier = this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier simpleGlobalField
            if accessFromPartition = partitionIdentifier then
                ComplexIdentifier.NameComplexIdentifier(fieldIdentifier)
            else
                let partitionContainerIdentifier = ComplexIdentifier.NameComplexIdentifier(partitionIdentifier)
                ComplexIdentifier.NestedComplexIdentifier(partitionContainerIdentifier,fieldIdentifier)
        else
            failwith "SimpleGlobalFields without context not supported yet"

   
    member this.transformSimpleGlobalFieldToAccessExpression (simpleGlobalField : SimpleGlobalField) (accessFromPartition:Identifier) =
        let varName = this.transformSimpleGlobalFieldToComplexIdentifier simpleGlobalField accessFromPartition
        NuXmvBasicExpression.ComplexIdentifierExpression (varName)
    
    member this.getFieldsToTransform (partition:Identifier) =
        let fields = toSimplifiedMetamodel.getSimpleGlobalFields
        let filterInCurrentPartition (field:SimpleGlobalField) =
            if field.hasContext then
                let context = field.getContext
                context.rootComponentName = partition.Name //return the boolean value of the comparision. Recall: This is no assignment
            else
                false
        fields |> List.filter filterInCurrentPartition

    member this.generateFieldDeclarationsOfPartition (partition:Identifier) : ModuleElement =
        let fieldsToTransform = this.getFieldsToTransform partition
        let generateDecl (field:SimpleGlobalField) : TypedIdentifier =
            let _simpleType = match field.getFieldSymbol.Type with
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

    member this.generateInitialisations (partition:Identifier) : SingleAssignConstraint list =
        let fieldsToTransform = this.getFieldsToTransform partition
        let generateSingleInit (field:SimpleGlobalField) =
            let identifier = this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier field |> ComplexIdentifier.NameComplexIdentifier
            let generateInitialValueExpression (initialValue:obj): BasicExpression =
                match initialValue with
                        | :? int as value -> value |> (fun value -> new bigint(value))
                                                   |> ConstExpression.IntegerConstant
                                                   |> BasicExpression.ConstExpression
                        | :? bool as value -> value |> ConstExpression.BooleanConstant
                                                    |> BasicExpression.ConstExpression
                        | _ -> failwith "NotImplementedYet"
            let initialValues = field.getInitialValues |> List.map generateInitialValueExpression
                                                          |> BasicExpression.SetExpression                
            SingleAssignConstraint.InitialStateAssignConstraint(identifier,initialValues)
        fieldsToTransform |> List.map generateSingleInit

    member this.generatePartition (partition:Identifier) : ModuleDeclaration =
        let fieldDecls = this.generateFieldDeclarationsOfPartition partition
        let otherPartitionIdentifier = []
        {
            ModuleDeclaration.Identifier = partition;
            ModuleDeclaration.ModuleParameters = otherPartitionIdentifier;
            ModuleDeclaration.ModuleElements = [fieldDecls];
        }
        

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
                    
    member this.transformSimpleExpression (expression:SimpleExpression) : NuXmvBasicExpression =
        match expression with
            | SimpleExpression.BooleanLiteral (value:bool) ->
                value |> NuXmvConstExpression.BooleanConstant
                      |> NuXmvBasicExpression.ConstExpression
            | SimpleExpression.IntegerLiteral (value:int) ->
                value |> (fun value -> new bigint(value))
                      |> NuXmvConstExpression.IntegerConstant 
                      |> NuXmvBasicExpression.ConstExpression
            | SimpleExpression.DecimalLiteral (value:decimal) ->
                value |> System.Decimal.ToDouble
                      |> NuXmvConstExpression.RealConstant 
                      |> NuXmvBasicExpression.ConstExpression                    
            | SimpleExpression.UnaryExpression (operand:SimpleExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformSimpleExpression operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> NuXmvBasicExpression.UnaryExpression(UnaryOperator.LogicalNot,transformedOperand)
                    | MMUnaryOperator.Minus      -> failwith "NotImplementedYet"
            | SimpleExpression.BinaryExpression (leftExpression:SimpleExpression, operator:MMBinaryOperator, rightExpression : SimpleExpression) ->
                let transformedLeft = this.transformSimpleExpression leftExpression
                let transformedRight = this.transformSimpleExpression rightExpression
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
            | SimpleExpression.FieldAccessExpression (field:SimpleGlobalField) ->
                this.transformSimpleGlobalFieldToAccessExpression field mainModuleIdentifier

    member this.transformWriteOnceStatement (statement:WriteOnceStatement) (accessFromPartition:Identifier) : SingleAssignConstraint =        
        let transformOption (option:WriteOnceOption) : CaseConditionAndEffect =        
            let transformedCondition = this.transformSimpleExpression option.getTakenDecisionsAsCondition
            let transformedEffect = this.transformSimpleExpression option.TargetEffect
            {
                CaseConditionAndEffect.CaseCondition = transformedCondition;
                CaseConditionAndEffect.CaseEffect = transformedEffect;
            }
        let transformedTarget = this.transformSimpleGlobalFieldToComplexIdentifier statement.Target accessFromPartition
        let effect = statement.Options |> List.map transformOption
                                       |> BasicExpression.CaseExpression
        SingleAssignConstraint.NextStateAssignConstraint(transformedTarget,effect)
    
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
                    