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



module internal SamToNuXmv =
    

    type ManageVariablesState = {
        TakenNames : Set<string>;
        VarWithPostValueToVarWithCurrentValue : Map<VcSam.Var,VcSam.Var>;
        VarWithCurrentValueToVarWithPostValue : Map<VcSam.Var,VcSam.Var>;
        VarToNuXmvIdentifier: Map<VcSam.Var,NuXmvIdentifier>;
        VarToNuXmvComplexIdentifier: Map<VcSam.Var,NuXmv.ComplexIdentifier>;
        // TODO: Add type information of a variable
        NameGenerator : NameGenerator;
    }
        with
            member private this.generateNewName (based_on:string) : string =
                this.NameGenerator this.TakenNames based_on
                
            member private this.generateNuXmvIdentifier (var:VcSam.Var) : (ManageVariablesState) =
                let nuXmvIdentifier = {NuXmvIdentifier.Name=var.getName}
                let nuXmvComplexIdentifier = NuXmv.ComplexIdentifier.NameComplexIdentifier(nuXmvIdentifier)
                let newState=
                    { this with
                        ManageVariablesState.VarToNuXmvIdentifier = this.VarToNuXmvIdentifier.Add (var,nuXmvIdentifier)
                        ManageVariablesState.VarToNuXmvComplexIdentifier = this.VarToNuXmvComplexIdentifier.Add (var,nuXmvComplexIdentifier)
                    }
                newState

            member private this.generatePostValueVar (currentValVar:VcSam.Var) : (VcSam.Var*ManageVariablesState) =
                let postValVarName = this.generateNewName (currentValVar.getName + "_virtual")
                let postValVar = VcSam.Var.Var(postValVarName)
                let newState=
                    { this with
                        ManageVariablesState.TakenNames = this.TakenNames.Add postValVarName;
                        ManageVariablesState.VarWithPostValueToVarWithCurrentValue =
                                this.VarWithPostValueToVarWithCurrentValue.Add (postValVar,currentValVar)
                        ManageVariablesState.VarWithCurrentValueToVarWithPostValue =
                                this.VarWithCurrentValueToVarWithPostValue.Add (currentValVar,postValVar)
                    }
                (postValVar,newState)

            member private this.createMapEntries (var:VcSam.Var) : ManageVariablesState =
                let (newVar,newState1) = this.generatePostValueVar var
                let newState2 = newState1.generateNuXmvIdentifier var
                newState2

            static member initial (variableDeclsToAdd:VcSam.GlobalVarDecl list) (nameGenerator:NameGenerator) =
                // * create a nuXmv identifier
                // * create a virtual variable with "virtualVar==next(var)"
                // Note: to avoid name clashes, every variable, which will be added, needs already to be in TakenNames

                let nuXmvKeywords: Set<string> = Set.empty<string>
                let takenVariableNames = variableDeclsToAdd |> List.map (fun varDecl -> varDecl.Var.getName) |> Set.ofList
                let initialState =
                    {
                        ManageVariablesState.TakenNames = Set.union nuXmvKeywords takenVariableNames;
                        ManageVariablesState.VarWithPostValueToVarWithCurrentValue = Map.empty<VcSam.Var,VcSam.Var>;
                        ManageVariablesState.VarWithCurrentValueToVarWithPostValue = Map.empty<VcSam.Var,VcSam.Var>;
                        ManageVariablesState.VarToNuXmvIdentifier = Map.empty<VcSam.Var,NuXmvIdentifier>;
                        ManageVariablesState.VarToNuXmvComplexIdentifier = Map.empty<VcSam.Var,NuXmv.ComplexIdentifier>;
                        ManageVariablesState.NameGenerator = nameGenerator;
                    }
                let variablesToAdd = variableDeclsToAdd |> List.map (fun varDecl -> varDecl.Var)
                    
                let generateAndAddToList (state:ManageVariablesState) (variableToAdd:VcSam.Var): (ManageVariablesState) =
                    let (newState) = state.createMapEntries variableToAdd
                    newState
                Seq.fold generateAndAddToList (initialState) variablesToAdd
            


    let generateGlobalVarDeclarations (manageVariablesState:ManageVariablesState) (varDecls:VcSam.GlobalVarDecl list) : ModuleElement =
        let generateDecl (varDecl:VcSam.GlobalVarDecl) : TypedIdentifier =
            let _type = match varDecl.Type with
                            | Sam.Type.BoolType -> TypeSpecifier.SimpleTypeSpecifier(SimpleTypeSpecifier.BooleanTypeSpecifier)
                            | Sam.Type.IntType -> TypeSpecifier.SimpleTypeSpecifier(SimpleTypeSpecifier.IntegerTypeSpecifier)
                            //| SamType.Decimal -> failwith "NotImplementedYet"
            let _variable = manageVariablesState.VarToNuXmvIdentifier.Item varDecl.Var
            {
                TypedIdentifier.Identifier = _variable ;
                TypedIdentifier.TypeSpecifier = _type ;
            }
        varDecls |> List.map generateDecl
                 |> ModuleElement.VarDeclaration
    
    let rec translateExpression (manageVariablesState:ManageVariablesState) (expr:VcSam.Expr) : NuXmvBasicExpression =
        match expr with
            | VcSam.Expr.Literal (_val) ->
                match _val with
                    | VcSam.Val.BoolVal(_val) -> NuXmvBasicExpression.ConstExpression(NuXmvConstExpression.BooleanConstant(_val))
                    | VcSam.Val.NumbVal(_val) -> NuXmvBasicExpression.ConstExpression(NuXmvConstExpression.IntegerConstant(_val))
            | VcSam.Expr.Read (_var) ->
                match manageVariablesState.VarWithPostValueToVarWithCurrentValue.TryFind _var with
                    | None ->
                        NuXmvBasicExpression.ComplexIdentifierExpression(manageVariablesState.VarToNuXmvComplexIdentifier.Item _var)
                    | Some(originalValue) ->
                        // here we have a virtual value. We want a next(originalValue) instead
                        NuXmvBasicExpression.BasicNextExpression(NuXmvBasicExpression.ComplexIdentifierExpression(manageVariablesState.VarToNuXmvComplexIdentifier.Item originalValue))
            | VcSam.Expr.ReadOld (_var) ->            
                match manageVariablesState.VarWithPostValueToVarWithCurrentValue.TryFind _var with
                    | None ->
                        NuXmvBasicExpression.ComplexIdentifierExpression(manageVariablesState.VarToNuXmvComplexIdentifier.Item _var)
                    | Some(originalValue) ->
                        failwith "not sure, what this should mean in combination with readOld"
            | VcSam.Expr.UExpr (expr,uop) ->
                let operator =
                    match uop with
                        | VcSam.UOp.Not -> NuXmv.UnaryOperator.LogicalNot
                NuXmvBasicExpression.UnaryExpression(operator,translateExpression manageVariablesState expr)
            | VcSam.Expr.BExpr (left, bop, right) ->
                let operator =
                    match bop with
                        | VcSam.BOp.Add -> NuXmv.BinaryOperator.IntegerAddition
                        | VcSam.BOp.Subtract -> NuXmv.BinaryOperator.IntegerSubtraction
                        | VcSam.BOp.Multiply -> NuXmv.BinaryOperator.IntegerMultiplication
                        | VcSam.BOp.Divide -> NuXmv.BinaryOperator.IntegerDivision
                        | VcSam.BOp.Modulo -> NuXmv.BinaryOperator.IntegerRemainder
                        | VcSam.BOp.And -> NuXmv.BinaryOperator.LogicalAnd
                        | VcSam.BOp.Or -> NuXmv.BinaryOperator.LogicalOr
                        | VcSam.BOp.Implies -> NuXmv.BinaryOperator.LogicalImplies
                        | VcSam.BOp.Equals -> NuXmv.BinaryOperator.Equality //TODO: For Binary Left and Right NuXmv.BinaryOperator.LogicalEquivalence should be better
                        | VcSam.BOp.NotEquals -> NuXmv.BinaryOperator.Inequality //TODO: For Binary Left and Right NuXmv.BinaryOperator.Xor should be better
                        | VcSam.BOp.Less -> NuXmv.BinaryOperator.LessThan
                        | VcSam.BOp.LessEqual -> NuXmv.BinaryOperator.LessEqual
                        | VcSam.BOp.Greater -> NuXmv.BinaryOperator.GreaterThan
                        | VcSam.BOp.GreaterEqual -> NuXmv.BinaryOperator.GreaterEqual
                NuXmvBasicExpression.BinaryExpression(translateExpression manageVariablesState left,operator,translateExpression manageVariablesState right)



    let generateGlobalVarInitialisations (manageVariablesState:ManageVariablesState) (varDecls:VcSam.GlobalVarDecl list) : ModuleElement =
        let generateInit (varDecl:Sam.GlobalVarDecl) : VcSam.Expr =
            let generatePossibleValues (initialValue : VcSam.Val) : VcSam.Expr =
                let assignVar = varDecl.Var
                let assignExpr = VcSam.Expr.Literal(initialValue)
                let operator = VcSam.BOp.Equals
                VcSam.Expr.BExpr(VcSam.Expr.Read(assignVar),operator,assignExpr)
            varDecl.Init |> List.map generatePossibleValues
                         |> VcSam.createOredExpr
        varDecls |> List.map generateInit
                 |> VcSam.createAndedExpr
                 |> translateExpression (manageVariablesState)
                 |> ModuleElement.InitConstraint

    let generateTransRelation (manageVariablesState:ManageVariablesState) (expr:VcSam.Expr) : ModuleElement =
        ModuleElement.TransConstraint(translateExpression manageVariablesState expr)

    
    let transformConfiguration (pgm:VcSam.Pgm) : NuXmvProgram =
        // create the manageVariablesState: Keeps the association between the post value variable and the current value variable
        // (the post variable value is purely "virtual". It will be replaced by "next(currentValue)" )
        let manageVariablesState = ManageVariablesState.initial pgm.Globals SafetySharp.FreshNameGenerator.namegenerator_c_like


        let formulaForWPPostcondition = // "a'=a,b'<->b,...."
            let createFormulaForGlobalVarDecl (globalVarDecl:VcSam.GlobalVarDecl) : VcSam.Expr =
                let varCurrent = globalVarDecl.Var
                let varPost = manageVariablesState.VarWithCurrentValueToVarWithPostValue.Item varCurrent
                let operator = VcSam.BOp.Equals
                VcSam.Expr.BExpr(VcSam.Expr.Read(varPost),operator,VcSam.Expr.Read(varCurrent))
            pgm.Globals |> List.map createFormulaForGlobalVarDecl
                        |> VcSam.createAndedExpr

                        
        // declare globals variables
        let globalVarModuleElement = generateGlobalVarDeclarations manageVariablesState pgm.Globals
        
        // initialize globals (INIT)
        let globalVarInitialisations = generateGlobalVarInitialisations manageVariablesState pgm.Globals
        
        // program loop (TRANS)
        let wp_of_Statement = VcWeakestPrecondition.wp pgm.Body formulaForWPPostcondition
        let transRelation  = generateTransRelation manageVariablesState wp_of_Statement
        
        let systemModule =
            {
                NuXmvModuleDeclaration.Identifier = {NuXmvIdentifier.Name = "system" };
                NuXmvModuleDeclaration.ModuleParameters = [];
                NuXmvModuleDeclaration.ModuleElements = [globalVarModuleElement;globalVarInitialisations;transRelation];
            }
        
        {
            NuXmvProgram.Modules = [systemModule];
            NuXmvProgram.Specifications = [];
        }




    open SafetySharp.Workflow
    open SafetySharp.Analysis.VerificationCondition

    type VcModelForModification = VcSamModelForModification.ModelForModification

    let transformConfiguration_fromVcSam : WorkflowFunction<VcModelForModification,NuXmvProgram,unit> = workflow {
        let reservedNames = Set.empty<string>
        do! SafetySharp.Analysis.VerificationCondition.VcsamrChangeIdentifier.changeIdentifiers reservedNames
        let! pgm = VcSamModelForModification.getVcSamModel
        let nuXmvProgram = transformConfiguration pgm
        do! updateState nuXmvProgram
    }
        
    let transformConfiguration_fromSam : WorkflowFunction<Sam.Pgm,NuXmvProgram,unit> = workflow {
        do! VcSamModelForModification.transformSamToVcSam
        do! transformConfiguration_fromVcSam
        return ()
    }

(*

type internal MetamodelToNuXmv (configuration:MMConfiguration)  =
    let toSimplifiedMetamodel = MetamodelToSimplifiedMetamodel(configuration)
    let toWriteOnceStatements = SimpleStatementsToWriteOnceStatements(toSimplifiedMetamodel.getSimpleGlobalFields)

    let mainModuleIdentifier = {Identifier.Name="main"}    
    let partitions = toSimplifiedMetamodel.getPartitions

    // To transform the metamodel to NuXmv, we take an intermediate step:
    //   metamodel -> simplified metamodel -> nuxmv code
    
    // THIS IS THE MAIN FUNCTION AND ENTRY POINT
    member this.transformConfiguration  : NuXmvProgram =
        //TODO: Correct semantics with bindings and correct "interleaving" of bindings and partitions

        let partitionModules = partitions |> List.map this.generatePartition

        let createPartitionInstantiation (partition:SimplePartitionIdentity) : TypedIdentifier =
            let moduleTypeSpecifier = 
                let parameters = this.getModuleParametersforPartitions None |> List.map (fun identifier -> BasicExpression.ComplexIdentifierExpression(ComplexIdentifier.NameComplexIdentifier(identifier)))
                {
                    ModuleTypeSpecifier.ModuleName = this.getPartitionModuleNameFromSimplePartition partition;
                    ModuleTypeSpecifier.ModuleParameters = parameters;
                }
            {
                TypedIdentifier.TypeSpecifier=TypeSpecifier.ModuleTypeSpecifier(moduleTypeSpecifier);
                TypedIdentifier.Identifier=this.getPartitionInstanceNameFromSimplePartition partition;
            }
        let partitionInstantiations = partitions |> List.map createPartitionInstantiation
        let moduleElements = [ModuleElement.VarDeclaration(partitionInstantiations)]

        let mainModule = 
            {
                ModuleDeclaration.Identifier = mainModuleIdentifier;
                ModuleDeclaration.ModuleElements = moduleElements;
                ModuleDeclaration.ModuleParameters = [];
            }
        {
            NuXmvProgram.Modules = mainModule::partitionModules;
            NuXmvProgram.Specifications = [];
        }
        
    
    member this.getModuleParametersforPartitions (skip:SimplePartitionIdentity option) : Identifier list =
        let filtered = if skip.IsSome then partitions |> List.filter (fun elem -> elem <> skip.Value) else partitions
        filtered |> List.map this.getPartitionInstanceNameFromSimplePartition
        
    member this.getPartitionModuleNameFromSimplePartition(partition:SimplePartitionIdentity): Identifier =
        {Identifier.Name=("P" + partition.RootComponentName)}

    member this.getPartitionInstanceNameFromSimplePartition(partition:SimplePartitionIdentity): Identifier =
        {Identifier.Name=("p" + partition.RootComponentName)}

    member this.getPartitionInstanceNameFromContext (context:Context): Identifier =
        {Identifier.Name=("p" + context.Partition.RootComponentName)}

    member this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier (simpleGlobalField : SimpleGlobalField) : Identifier =
        // only use, when we know that simpleGlobalField is in the partition, the method calling this function, has
        // the partition of the simpleGlobalField in mind.
        if not simpleGlobalField.hasContext then
            failwith "SimpleGlobalFields in this function must belong to a partition"
        let flatSubcomponentName (context:Context) : string =
            let itemsInOrderRootToLeaf =
                context.HierarchicalAccess |> List.rev //the order should be root::subcomponent::leafSubcomponent
            itemsInOrderRootToLeaf |> List.map (fun elem -> sprintf "c%s_" elem)
                                   |> String.concat ""
        
        let kindOfFieldSymbol = if toSimplifiedMetamodel.isFieldInAComponent simpleGlobalField then "f" else "a"
        let fieldName = kindOfFieldSymbol+simpleGlobalField.getFieldSymbol.Name
        let flattenedNameOfField = (flatSubcomponentName simpleGlobalField.getContext) + fieldName;
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
                if not (context.Partition.RootComponentName = "") then
                    this.getPartitionInstanceNameFromContext context
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
    
    member this.getFieldsToTransform (partition:SimplePartitionIdentity) =
        // TODO: A bit ugly right now: this method relies on side effects and must be executed _after_ the transformation of the sequence
        let fields = toWriteOnceStatements.getAllFields()
        let filterInCurrentPartition (field:SimpleGlobalField) =
            if field.hasContext then
                let context = field.getContext
                context.Partition = partition //return the boolean value of the comparision. Recall: This is no assignment
            else
                false
        fields |> List.filter filterInCurrentPartition

    member this.generateFieldDeclarationsOfPartition (partition:SimplePartitionIdentity) : ModuleElement =
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

    member this.generateInitialisations (partition:SimplePartitionIdentity) : SingleAssignConstraint list =
        let fieldsToTransform = this.getFieldsToTransform partition
        let generateSingleInit (field:SimpleGlobalField) =
            let identifier = this.transformSimpleGlobalFieldInCurrentPartitionToIdentifier field |> ComplexIdentifier.NameComplexIdentifier
            let generateInitialValueExpression (initialValue:SimpleConstLiteral): BasicExpression =
                match initialValue with
                        | SimpleConstLiteral.IntegerLiteral (value) -> 
                            value |> (fun value -> new bigint(value))
                                  |> ConstExpression.IntegerConstant
                                  |> BasicExpression.ConstExpression
                        | SimpleConstLiteral.BooleanLiteral (value) ->
                             value |> ConstExpression.BooleanConstant
                                   |> BasicExpression.ConstExpression
                        | SimpleConstLiteral.DecimalLiteral (value) ->
                            value |> System.Decimal.ToDouble
                                  |> ConstExpression.RealConstant 
                                  |> BasicExpression.ConstExpression

            let initialValues = field.getInitialValues |> List.map generateInitialValueExpression
                                                          |> BasicExpression.SetExpression                
            SingleAssignConstraint.InitialStateAssignConstraint(identifier,initialValues)
        fieldsToTransform |> List.map generateSingleInit

         
    member this.generatePartitionUpdateCode (partition:SimplePartitionIdentity) : ModuleElement list=
        let partitionUpdateInSimpleStatements = toSimplifiedMetamodel.partitionUpdateInSimpleStatements partition
        let partitionUpdateInWriteOnlyStatements = toWriteOnceStatements.simpleStatementToWriteOnceStatements toSimplifiedMetamodel.getSimpleGlobalFields partitionUpdateInSimpleStatements
        let transformedWriteOnlyStatements = partitionUpdateInWriteOnlyStatements |> List.map (this.transformWriteOnceStatement (this.getPartitionInstanceNameFromSimplePartition partition))
        transformedWriteOnlyStatements

    member this.generatePartition (partition:SimplePartitionIdentity) : ModuleDeclaration =
        // TODO: remove parameter with identifier of this partition, if it is the partition itself. Use this.getModuleParametersforPartitions (Some(partition))
        // TODO: pretty ugly right now: partitionUpdateCode has to be generated before the fieldDeclaration, because
        //       this code has side effects in "toWriteOnceStatements" (generation of artificial fields)
        let partitionUpdateCode = this.generatePartitionUpdateCode partition
        let fieldDecls = this.generateFieldDeclarationsOfPartition partition
        let fieldInits = this.generateInitialisations partition |> ModuleElement.AssignConstraint
        let otherPartitionIdentifier = this.getModuleParametersforPartitions (None)
        {
            ModuleDeclaration.Identifier = this.getPartitionModuleNameFromSimplePartition partition;
            ModuleDeclaration.ModuleParameters = otherPartitionIdentifier;
            ModuleDeclaration.ModuleElements = fieldDecls::fieldInits::partitionUpdateCode;
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
            | MMExpression.ReadField (field:MMFieldSymbol, componentReference:MMComponentReferenceSymbol option) ->
                if componentReference.IsNone then
                    //called inside a component
                    failwith "Use transformExpressionInsideAFormula only for expression inside untransformed formulas and not in components"
                else
                    //called inside a formula
                    let simpleGlobalField = toSimplifiedMetamodel.resolveFieldAccessInsideAFormula componentReference.Value field
                    this.transformSimpleGlobalFieldToAccessExpression simpleGlobalField mainModuleIdentifier
            | MMExpression.ReadLocal (local:MMLocalSymbol) ->
                failwith "NotImplementedYet"
            | MMExpression.ReadParameter (parameter:MMParameterSymbol) ->
                failwith "NotImplementedYet"
    
    member this.transformSimpleConstLiteral (literal:SimpleConstLiteral) : NuXmvBasicExpression =
        match literal with
            | SimpleConstLiteral.BooleanLiteral (value:bool) ->
                value |> NuXmvConstExpression.BooleanConstant
                      |> NuXmvBasicExpression.ConstExpression
            | SimpleConstLiteral.IntegerLiteral (value:int) ->
                value |> (fun value -> new bigint(value))
                      |> NuXmvConstExpression.IntegerConstant 
                      |> NuXmvBasicExpression.ConstExpression
            | SimpleConstLiteral.DecimalLiteral (value:decimal) ->
                value |> System.Decimal.ToDouble
                      |> NuXmvConstExpression.RealConstant 
                      |> NuXmvBasicExpression.ConstExpression
    
    member this.transformBinaryOperator (operator:MMBinaryOperator) : BinaryOperator =
        match operator with
            | MMBinaryOperator.Add                -> BinaryOperator.IntegerAddition
            | MMBinaryOperator.Subtract           -> BinaryOperator.IntegerSubtraction
            | MMBinaryOperator.Multiply           -> BinaryOperator.IntegerMultiplication
            | MMBinaryOperator.Divide             -> BinaryOperator.IntegerDivision
            | MMBinaryOperator.Modulo             -> BinaryOperator.IntegerRemainder
            | MMBinaryOperator.LogicalAnd         -> BinaryOperator.LogicalAnd
            | MMBinaryOperator.LogicalOr          -> BinaryOperator.LogicalOr
            | MMBinaryOperator.Equals             -> BinaryOperator.Equality
            | MMBinaryOperator.NotEquals          -> BinaryOperator.Inequality
            | MMBinaryOperator.LessThan           -> BinaryOperator.LessThan
            | MMBinaryOperator.LessThanOrEqual    -> BinaryOperator.LessEqual
            | MMBinaryOperator.GreaterThan        -> BinaryOperator.GreaterThan
            | MMBinaryOperator.GreaterThanOrEqual -> BinaryOperator.GreaterEqual

    member this.transformSimpleExpression (expression:SimpleExpression) : NuXmvBasicExpression =
        match expression with
            | SimpleExpression.ConstLiteral (literal:SimpleConstLiteral) ->
                this.transformSimpleConstLiteral literal
            | SimpleExpression.UnaryExpression (operand:SimpleExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformSimpleExpression operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> NuXmvBasicExpression.UnaryExpression(UnaryOperator.LogicalNot,transformedOperand)
                    | MMUnaryOperator.Minus      -> failwith "NotImplementedYet"
            | SimpleExpression.BinaryExpression (leftExpression:SimpleExpression, operator:MMBinaryOperator, rightExpression : SimpleExpression) ->
                let transformedLeft = this.transformSimpleExpression leftExpression
                let transformedRight = this.transformSimpleExpression rightExpression
                let transformedOperator = this.transformBinaryOperator operator
                NuXmvBasicExpression.BinaryExpression(transformedLeft,transformedOperator,transformedRight)                
            | SimpleExpression.FieldAccessExpression (field:SimpleGlobalField) ->
                this.transformSimpleGlobalFieldToAccessExpression field mainModuleIdentifier

    member this.transformWriteOnceExpression (expression:WriteOnceExpression) : NuXmvBasicExpression =
        match expression with
            | WriteOnceExpression.ConstLiteral (literal:SimpleConstLiteral) ->
                this.transformSimpleConstLiteral literal
            | WriteOnceExpression.UnaryExpression (operand:WriteOnceExpression, operator:MMUnaryOperator) ->
                let transformedOperand = this.transformWriteOnceExpression operand
                match operator with
                    | MMUnaryOperator.LogicalNot -> NuXmvBasicExpression.UnaryExpression(UnaryOperator.LogicalNot,transformedOperand)
                    | MMUnaryOperator.Minus      -> failwith "NotImplementedYet"
            | WriteOnceExpression.BinaryExpression (leftExpression:WriteOnceExpression, operator:MMBinaryOperator, rightExpression : WriteOnceExpression) ->
                let transformedLeft = this.transformWriteOnceExpression leftExpression
                let transformedRight = this.transformWriteOnceExpression rightExpression
                let transformedOperator = this.transformBinaryOperator operator
                NuXmvBasicExpression.BinaryExpression(transformedLeft,transformedOperator,transformedRight)                
            | WriteOnceExpression.FieldAccessExpression (timeOfAccess:WriteOnceTimeOfAccess,field:SimpleGlobalField) ->
                match timeOfAccess with
                    | WriteOnceTimeOfAccess.UseResultOfLastStep ->
                        this.transformSimpleGlobalFieldToAccessExpression field mainModuleIdentifier
                    | WriteOnceTimeOfAccess.UseResultOfThisStep ->
                        this.transformSimpleGlobalFieldToAccessExpression field mainModuleIdentifier |> NuXmvBasicExpression.BasicNextExpression
    
    member this.transformWriteOnceStatement (accessFromPartition:Identifier) (statement:WriteOnceStatement) : ModuleElement =
        let transformedTarget = this.transformSimpleGlobalFieldToComplexIdentifier statement.getTarget accessFromPartition
        match statement with
            | WriteOnceStatementEvaluateDecisionsParallel (target:WriteOnceGlobalField, possibleEffects:WriteOncePossibleEffect list, elseEffect:WriteOnceEffectOnTarget) ->  
                (* old system:
                    convert to sequential decision and transform the sequential decision
                    let convertedToSequentialDecision = statement.convertToDecisionsSequential
                    this.transformWriteOnceStatement accessFromPartition convertedToSequentialDecision
                *)
                (* new system:
                    see also topic "How I can get non-deterministic behavior" on [nusmv-users]-Mailing List:
                    https://list.fbk.eu/sympa/arc/nusmv-users/2014-06/msg00002.html
                    TRANS
                        ( left_expression_1 -> next(variable)=right_expression_1) |
                        ( left_expression_2 -> next(variable)=right_expression_2) |
                        ...
                        ( left_expression_N -> next(variable)=right_expression_N)
                *)
                let transformedNextTarget = transformedTarget |> NextExpression.ComplexIdentifierExpression |> NextExpression.BasicNextExpression
                let transformOption (option:WriteOncePossibleEffect) =
                    let transformedCondition = this.transformWriteOnceExpression option.getTakenDecisionsAsCondition                    
                    let transformedEffect = option.TargetEffect.getEffects
                                                |> List.map (fun effect -> this.transformWriteOnceExpression effect)
                                                |> BasicExpression.SetExpression
                    let nextState = NextExpression.BinaryExpression(transformedNextTarget,BinaryOperator.Equality,transformedEffect)
                    NextExpression.BinaryExpression(transformedCondition,BinaryOperator.LogicalImplies,nextState)
                let transformedElse =
                    // if every other case doesn't match
                    let transformedCondition =
                        possibleEffects |> List.map (fun effect -> effect.getTakenDecisionsAsCondition)
                                        |> List.map (fun decision -> WriteOnceExpression.UnaryExpression(decision,MMUnaryOperator.LogicalNot))
                                        |> WriteOnceExpression.concatenateWithAnd
                                        |> this.transformWriteOnceExpression
                    let transformedEffect = elseEffect.getEffects
                                                |> List.map (fun effect -> this.transformWriteOnceExpression effect)
                                                |> BasicExpression.SetExpression
                    let nextState = NextExpression.BinaryExpression(transformedNextTarget,BinaryOperator.Equality,transformedEffect)
                    NextExpression.BinaryExpression(transformedCondition,BinaryOperator.LogicalImplies,nextState)
                let transformedOptions = possibleEffects |> List.map transformOption 
                let concatenatedWithOr = NuXmvAstHelpers.concatenateWithOr (transformedOptions@[transformedElse])
                ModuleElement.TransConstraint(concatenatedWithOr)
            | WriteOnceStatementEvaluateDecisionsSequential (target:WriteOnceGlobalField, possibleEffects:WriteOncePossibleEffect list) ->
                let transformOption (option:WriteOncePossibleEffect) : CaseConditionAndEffect =        
                    let transformedCondition = this.transformWriteOnceExpression option.getTakenDecisionsAsCondition
                    //let condition = bothDecisions.Tail |> List.fold (fun acc elem -> NuXmvBasicExpression.BinaryExpression(elem,BinaryOperator.LogicalAnd,acc)) bothDecisions.Head
                    let transformedEffect = option.TargetEffect.getEffects
                                                |> List.map (fun effect -> this.transformWriteOnceExpression effect)
                                                |> BasicExpression.SetExpression
                    {
                        CaseConditionAndEffect.CaseCondition = transformedCondition;
                        CaseConditionAndEffect.CaseEffect = transformedEffect;
                    }                
                let effect = possibleEffects |> List.map transformOption
                                             |> BasicExpression.CaseExpression
                ModuleElement.AssignConstraint([SingleAssignConstraint.NextStateAssignConstraint(transformedTarget,effect)])
            | WriteOnceStatementSimpleAssignWithCondition (target:WriteOnceGlobalField, effect:WriteOncePossibleEffect) ->
                // Isn't used right now. But consider: What to do, if "effect.TakenDecisions" doesn't match. Which value should be assigned to the targetField?
                // If it isn't used in the near future, delete it!
                failwith "NotImplementedYet"
            | WriteOnceStatementSimpleAssign (target:WriteOnceGlobalField, effect:WriteOnceExpression) ->
                let transformedEffect = this.transformWriteOnceExpression effect
                ModuleElement.AssignConstraint([SingleAssignConstraint.NextStateAssignConstraint(transformedTarget,transformedEffect)])

   
    
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