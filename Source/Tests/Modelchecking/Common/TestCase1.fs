namespace SafetySharp.Tests.Modelchecking


open SafetySharp.Modelchecking.PromelaSpin
open SafetySharp.Metamodel

type MMUnaryFormulaOperator = SafetySharp.Metamodel.UnaryFormulaOperator
type MMBinaryOperator = SafetySharp.Metamodel.BinaryOperator

module TestCase1 =    
    
    // Expressions I
    let booleanTrueExpression = Expression.BooleanLiteral(true)
    let booleanFalseExpression = Expression.BooleanLiteral(false)

    // Symbols
    let fieldXType = TypeSymbol.Boolean
    let fieldXSymbol = { FieldSymbol.Name="x"; FieldSymbol.Type=fieldXType; }
    let updateMethodReturnType = None
    let updateMethodSymbol = { MethodSymbol.Name="irrelevant"; MethodSymbol.ReturnType=updateMethodReturnType; MethodSymbol.Parameters=[]; }
    let indeterministicComponentSymbolName = "indeterministic Component Symbol..."
    let indeterministicComponentSymbol = { ComponentSymbol.Name=indeterministicComponentSymbolName; ComponentSymbol.UpdateMethod=updateMethodSymbol; ComponentSymbol.Methods=[]; ComponentSymbol.Fields=[fieldXSymbol]; }
    let indeterministicComponentReferenceSymbolName = "Reference to the root of a partition of the Type defined in 'indeterministic Component Symbol'..."
    let indeterministicComponentReferenceSymbolForFormulaUse = { ComponentReferenceSymbol.Name=indeterministicComponentReferenceSymbolName; ComponentReferenceSymbol.ComponentSymbol=indeterministicComponentSymbol; }
    let partitionASymbol = { PartitionSymbol.Name="partition A Symbol"; PartitionSymbol.RootComponent=indeterministicComponentSymbol; }
    let todo1 = [indeterministicComponentReferenceSymbolForFormulaUse] //not sure, if it should actually be added, because it is not actually a subcomponent of any componentsymbol
    let testCase1ModelSymbol = { ModelSymbol.Partitions=[partitionASymbol]; ModelSymbol.ComponentSymbols=[indeterministicComponentSymbol] ; ModelSymbol.Subcomponents=([(indeterministicComponentSymbol,[])] |> Map.ofList ) ; ModelSymbol.ComponentObjects=todo1  }
    
    // Expressions II
    let fieldXExpressionInComponent = Expression.FieldAccessExpression(fieldXSymbol,None)
    let fieldXExpressionInFormula = Expression.FieldAccessExpression(fieldXSymbol,Some(indeterministicComponentReferenceSymbolForFormulaUse))

    // Statements
    let assignTrueStatement = Statement.AssignmentStatement(fieldXExpressionInComponent,booleanTrueExpression)
    let assignFalseStatement = Statement.AssignmentStatement(fieldXExpressionInComponent,booleanFalseExpression)
    let assignTrueOption = (booleanTrueExpression,assignTrueStatement)
    let assignFalseOption = (booleanTrueExpression,assignFalseStatement)
    let indeterministicStatement = Statement.GuardedCommandStatement([assignTrueOption;assignFalseOption])

    // Objects I
    let fieldXObject = { FieldObject.FieldSymbol=fieldXSymbol; FieldObject.InitialValues=[true;false]; }
    let indeterministicComponentObjectName = indeterministicComponentReferenceSymbolName //TODO: Not sure, if this is correct. I assume it is
    let indeterministicComponentObject = { ComponentObject.Name=indeterministicComponentObjectName; ComponentObject.ComponentSymbol=indeterministicComponentSymbol ; ComponentObject.Fields=([(fieldXSymbol,fieldXObject)] |> Map.ofList); ComponentObject.Subcomponents=([]|>Map.ofList ); }
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

