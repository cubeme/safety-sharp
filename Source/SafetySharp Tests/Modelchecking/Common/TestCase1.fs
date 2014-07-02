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

namespace SafetySharp.Tests.Modelchecking


open SafetySharp.Internal.Modelchecking.PromelaSpin
open SafetySharp.Internal.Metamodel

type internal MMUnaryFormulaOperator = SafetySharp.Internal.Metamodel.UnaryFormulaOperator
type internal MMBinaryOperator = SafetySharp.Internal.Metamodel.BinaryOperator

module internal TestCase1 =    
    
    // Expressions I
    let booleanTrueExpression = Expression.BooleanLiteral(true)
    let booleanFalseExpression = Expression.BooleanLiteral(false)

    // Symbols
    let fieldXType = TypeSymbol.Boolean
    let fieldXSymbol = { FieldSymbol.Name="x"; FieldSymbol.Type=fieldXType; }
    let updateMethodReturnType = None
    let updateMethodSymbol = { MethodSymbol.Name="irrelevant"; MethodSymbol.ReturnType=updateMethodReturnType; MethodSymbol.Parameters=[];Locals = [] }
    let indeterministicComponentSymbolName = "indeterministic Component Symbol..."
    let indeterministicComponentSymbol = { ComponentSymbol.Name=indeterministicComponentSymbolName; ComponentSymbol.UpdateMethod=Some updateMethodSymbol; ComponentSymbol.RequiredPorts=[]; ComponentSymbol.ProvidedPorts=[]; ComponentSymbol.Fields=[fieldXSymbol]; }
    let indeterministicComponentReferenceSymbolName = "Reference to the root of a partition of the Type defined in 'indeterministic Component Symbol'..."
    let indeterministicComponentReferenceSymbolForFormulaUse = { ComponentReferenceSymbol.Name=indeterministicComponentReferenceSymbolName; ComponentReferenceSymbol.ComponentSymbol=indeterministicComponentSymbol; }
    let partitionASymbol = { PartitionSymbol.Name="partition A Symbol"; PartitionSymbol.RootComponent=indeterministicComponentSymbol; }
    let todo1 = [indeterministicComponentReferenceSymbolForFormulaUse] //not sure, if it should actually be added, because it is not actually a subcomponent of any componentsymbol
    let testCase1ModelSymbol = { ModelSymbol.Partitions=[partitionASymbol]; ModelSymbol.ComponentSymbols=[indeterministicComponentSymbol] ; ModelSymbol.Subcomponents=([(indeterministicComponentSymbol,[])] |> Map.ofList ) ; ModelSymbol.ComponentObjects=todo1  }
    
    // Expressions II
    let fieldXExpressionInComponent = Expression.ReadField(fieldXSymbol,None)
    let fieldXExpressionInFormula = Expression.ReadField(fieldXSymbol,Some(indeterministicComponentReferenceSymbolForFormulaUse))

    // Statements
    let assignTrueStatement = Statement.WriteField(fieldXSymbol,booleanTrueExpression)
    let assignFalseStatement = Statement.WriteField(fieldXSymbol,booleanFalseExpression)
    let assignTrueOption = (booleanTrueExpression,assignTrueStatement)
    let assignFalseOption = (booleanTrueExpression,assignFalseStatement)
    let indeterministicStatement = Statement.GuardedCommandStatement([assignTrueOption;assignFalseOption])

    // Objects I
    let fieldXObject = { FieldObject.FieldSymbol=fieldXSymbol; FieldObject.InitialValues=[true;false]; }
    let indeterministicComponentObjectName = indeterministicComponentReferenceSymbolName //TODO: Not sure, if this is correct. I assume it is
    let indeterministicComponentObject = { ComponentObject.Name=indeterministicComponentObjectName; ComponentObject.ComponentSymbol=indeterministicComponentSymbol ; ComponentObject.Fields=([(fieldXSymbol,fieldXObject)] |> Map.ofList); ComponentObject.Subcomponents=([]|>Map.ofList ); Bindings = Map.empty }
    let partitionAObject = { PartitionObject.PartitionSymbol=partitionASymbol; PartitionObject.RootComponent=indeterministicComponentObject; }
    
    // MethodBodyResolver
    let methodBodyResolver = ([((indeterministicComponentSymbol,updateMethodSymbol),indeterministicStatement)] |> Map.ofList)

    // Formulas
    let expressionFieldXIsTrue = Expression.BinaryExpression(fieldXExpressionInFormula,MMBinaryOperator.Equals,booleanTrueExpression)
    let formulaFieldXAlwaysTrue = Formula.UnaryFormula(Formula.StateFormula(expressionFieldXIsTrue),MMUnaryFormulaOperator.Globally)

    // Objects II (Model and Configuration)
    // TODO: why is ModelSymbol in Configuration and in ModelObject????
    let testCase1ModelObject = { ModelObject.ModelSymbol=testCase1ModelSymbol; ModelObject.Partitions=[partitionAObject]; ModelObject.ComponentObjects= ([(indeterministicComponentReferenceSymbolForFormulaUse,indeterministicComponentObject)] |> Map.ofList);}
    let testCase1Configuration = { Configuration.ModelSymbol=testCase1ModelSymbol; Configuration.ModelObject=testCase1ModelObject; Configuration.Formulas=[formulaFieldXAlwaysTrue]; Configuration.MethodBodyResolver=methodBodyResolver; }

module internal TestCase1Simplified =

    open SafetySharp.Internal.Modelchecking

    // Expressions
    let booleanTrueExpression = SimpleExpression.ConstLiteral(SimpleConstLiteral.BooleanLiteral(true))
    let booleanFalseExpression = SimpleExpression.ConstLiteral(SimpleConstLiteral.BooleanLiteral(false))
    
    // Context and Partition
    let simplePartition = {
        SimplePartitionIdentity.RootComponentName = "root1";
    }
    let contextComponent = {
        Context.HierarchicalAccess = [];
        Context.Partition = simplePartition;
    }

    // Fields
    let initialValues = [SimpleConstLiteral.BooleanLiteral(true);SimpleConstLiteral.BooleanLiteral(false)]
    let simpleFieldXSymbol = { SimpleFieldSymbol.Name="x"; SimpleFieldSymbol.Type=TestCase1.fieldXType; }
    let simpleGlobalFieldWithContext = {
        SimpleGlobalFieldWithContext.Context=contextComponent;
        SimpleGlobalFieldWithContext.FieldSymbol=simpleFieldXSymbol;
        SimpleGlobalFieldWithContext.InitialValues=initialValues;
    }
    let field = SimpleGlobalField.FieldWithContext(simpleGlobalFieldWithContext)

    // Statements
    let assignStatementTrue = SimpleStatement.AssignmentStatement(field,booleanTrueExpression)
    let assignStatementFalse = SimpleStatement.AssignmentStatement(field,booleanFalseExpression)
    let guardedCommandStatement = SimpleStatement.GuardedCommandStatement([(booleanTrueExpression,[assignStatementTrue]);
                                                                           (booleanTrueExpression,[assignStatementFalse])])
    
    // Outputs
    let fields = [field]
    let partitionFields = [field]
    let partitionUpdate = [guardedCommandStatement]
