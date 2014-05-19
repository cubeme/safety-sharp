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

namespace SafetySharp.Modelchecking.Promela
{
    using System;
    using System.Collections.Generic;
    using System.Collections.Immutable;
    using System.Linq;
    using System.Text;
    using Metamodel.Types;
    using Microsoft.CodeAnalysis;
    using Modeling;
    using Utilities;
    using MM = Metamodel;
    using MMExpressions = Metamodel.Expressions;
    using MMStatements = Metamodel.Statements;
    using MMConfigurations = Metamodel.Configurations;
    using MMDeclarations = Metamodel.Declarations;
    using PrExpression = Expressions.Expression;
    using PrStatement = Statements.Statement;
    using PrExpressions = Expressions;
    using PrStatements = Statements;

    #region Expressions

    internal struct ComponentInstanceScope
    {
        public ImmutableArray<MM.Identifier> Identifiers { get; set; }
    };

    internal struct FieldInfo
    {
        //internal ImmutableArray<MM.Identifier> ComponentInstanceNames;
        internal ComponentInstanceScope AffectedComponentScope;
        internal MMDeclarations.FieldDeclaration FieldDeclaration;
        internal MM.Identifier Fieldname;
        internal MMConfigurations.ValueArray InitialValues;

        internal string GetName()
        {
            var namestring = new StringBuilder();
            foreach(var identifier in AffectedComponentScope.Identifiers) namestring.Append(identifier.Name + "_");
            namestring.Append(Fieldname.Name);
            return namestring.ToString();
        }
    }

    internal struct ComponentConfigurationUpdateMethod
    {
        internal MMConfigurations.ComponentConfiguration AffectedComponentConfiguration;
        internal ComponentInstanceScope AffectedComponentScope;
        internal MMStatements.Statement UpdateMethod;
    }

    internal static class PromelaHelpers
    {
        public static PrExpressions.BooleanLiteral ConstTrueExpression()
        {
            return new PrExpressions.BooleanLiteral(true);
        }

        public static PrExpressions.BooleanLiteral ConstFalseExpression()
        {
            return new PrExpressions.BooleanLiteral(false);
        }

        public static PrStatement CoverStatementInEndlessLoop(PrStatement statement)
        {
            var trueGuard = new PrExpressions.BooleanLiteral(true);
            var clause = new PrStatements.GuardedCommandExpressionClause(trueGuard, statement);
            return new PrStatements.GuardedCommandRepetitionStatement(
                ImmutableArray<PrStatements.GuardedCommandClause>.Empty.Add(clause));
        }

        public static PrStatement SimpleFieldAssignment(string fieldName, PrExpression expr)
        {
            return new PrStatements.AssignmentStatement(new PrExpressions.VariableReferenceExpression(fieldName, null, null), expr);
        }
    }

    internal class MetamodelToPromela
    {
        public readonly MM.MetamodelConfiguration Mm;
        public readonly MM.MetamodelResolver MmAccessTypeToConcreteTypeDictionary;

        public readonly ImmutableArray<FieldInfo> MmFieldList;

        public IImmutableDictionary<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>> MmFieldDictionary;
        //MmComponentInstanceHierarchieAndFieldIdentifierToFieldInfoDictionary;

        public MetamodelToPromela(MM.MetamodelConfiguration mm, MM.MetamodelResolver metamodelResolver)
        {
            Mm = mm;
            MmAccessTypeToConcreteTypeDictionary = metamodelResolver;
            var extractedFields = ExtractFields(Mm, MmAccessTypeToConcreteTypeDictionary);
            MmFieldList = extractedFields.MmFieldList;
            MmFieldDictionary = extractedFields.MmFieldDictionary;
        }

        public MetamodelExpressionToPromelaExpression GetExpressionVisitor(ComponentInstanceScope currentComponent)
        {
            return new MetamodelExpressionToPromelaExpression(this, currentComponent);
        }

        public MetamodelStatementToPromelaStatement GetStatementVisitor(ComponentInstanceScope currentComponent)
        {
            return new MetamodelStatementToPromelaStatement(this, currentComponent);
        }

        //this is the top level element of a meta model
        public Proctype ConvertMetaModelConfiguration()
        {
            var fieldDeclarations = GenerateFieldDeclarations();

            var systemSteps = Mm.Partitions.SelectMany(partition => ImmutableArray<PrStatement>.Empty
                                                           .Add(GenerateUpdateStatements(partition, MmFieldList))
                                                           .Add(GenerateBindingExecutionStatements(partition, MmFieldList)));
            var systemStepsBlock = new PrStatements.SimpleBlockStatement(systemSteps.AsImmutable());

            var systemLoop = PromelaHelpers.CoverStatementInEndlessLoop(systemStepsBlock);

            var code = fieldDeclarations.Add(systemLoop);
            var systemProctype = new Proctype(true, "System", code);

            return systemProctype;
        }

        public PromelaTypeName ConvertType(TypeSymbol type)
        {
            if (type is VoidType)
                throw new NotImplementedException();
            if (type is BooleanType)
                return PromelaTypeName.Bool;
            if (type is IntegerType)
                return PromelaTypeName.Int;
            if (type is DecimalType)
                throw new NotImplementedException();
            if (type is InterfaceType)
                throw new NotImplementedException();
            throw new NotImplementedException();
        }

        public PrExpressions.ConstExpression ConvertObject(MMConfigurations.Value mmValue, TypeSymbol type)
        {
            if (type is VoidType)
                throw new NotImplementedException();
            if (type is BooleanType)
            {
                var value = (bool)mmValue.Object;
                return new PrExpressions.BooleanLiteral(value);
            }
            if (type is IntegerType)
            {
                var value = (int)mmValue.Object;
                return new PrExpressions.NumberLiteral(value);
            }
            if (type is DecimalType)
                throw new NotImplementedException();
            if (type is InterfaceType)
                throw new NotImplementedException();
            throw new NotImplementedException();
        }

        public ImmutableArray<PrStatement> GenerateFieldDeclarations()
        {
            var statements = MmFieldList.SelectMany(field =>
            {
                var type = field.FieldDeclaration.Type;
                var name = field.GetName();
                var declStatement = new PrStatements.DeclarationStatement(ConvertType(type), name, 1, null);
                var initialvalueClauses = field.InitialValues.Values.Select(
                    value =>
                    {
                        var prValue = ConvertObject(value, type);
                        var clause = new PrStatements.GuardedCommandExpressionClause(PromelaHelpers.ConstTrueExpression(),
                                                                                     PromelaHelpers.SimpleFieldAssignment(name, prValue));
                        return (PrStatements.GuardedCommandClause)clause;
                    });
                var initialValueStatement = new PrStatements.GuardedCommandSelectionStatement(initialvalueClauses.ToImmutableArray());
                return (new PrStatement[] { declStatement, initialValueStatement });
            });
            return statements.ToImmutableArray();
        }

        public ImmutableArray<ComponentConfigurationUpdateMethod> CollectUpdateMethodsInOrder(MMConfigurations.Partition partition)
        {
            var scope = new ComponentInstanceScope() { Identifiers = ImmutableArray<MM.Identifier>.Empty };
            return CollectUpdateMethodsInOrder(partition.Component, scope);
        }
        public ImmutableArray<ComponentConfigurationUpdateMethod> CollectUpdateMethodsInOrder(MMConfigurations.ComponentConfiguration component, ComponentInstanceScope parentScope )
        {
            var updateMethods = new List<ComponentConfigurationUpdateMethod>();
            var scope = new ComponentInstanceScope() {Identifiers = parentScope.Identifiers.Add(component.Identifier) };
            var componentDeclaration = this.MmAccessTypeToConcreteTypeDictionary.Resolve(component.Type);
            var updateMethod = new ComponentConfigurationUpdateMethod
            {
                AffectedComponentScope = scope,
                AffectedComponentConfiguration = component,
                UpdateMethod = componentDeclaration.UpdateMethod.Body
            };
            updateMethods.Add(updateMethod);
            
            foreach (var componentConfiguration in component.SubComponents)
            {
                updateMethods.AddRange(CollectUpdateMethodsInOrder(componentConfiguration, scope));
            }
            return updateMethods.ToImmutableArray();
        }

        public PrStatement GenerateUpdateStatements(MMConfigurations.Partition partition, ImmutableArray<FieldInfo> fields)
        {
            var promelaUpdateStatements = new List<PrStatement>();
            var updateMethods = CollectUpdateMethodsInOrder(partition);
            foreach (var componentConfigurationUpdateMethod in updateMethods)
            {
                var visitor= this.GetStatementVisitor(componentConfigurationUpdateMethod.AffectedComponentScope);
                var promelaUpdateStatement = componentConfigurationUpdateMethod.UpdateMethod.Accept(visitor);
                promelaUpdateStatements.Add(promelaUpdateStatement);
            }
            return new PrStatements.SimpleBlockStatement(promelaUpdateStatements.AsImmutable());
        }

        public PrStatement GenerateBindingExecutionStatements(MMConfigurations.Partition partition, ImmutableArray<FieldInfo> fields)
        {
            throw new NotImplementedException();
        }

        public static ExtractFieldsTuple ExtractFields(MMConfigurations.ComponentConfiguration comp,
                                                       ComponentInstanceScope parentScope,
                                                       MM.MetamodelResolver mmAccessTypeToConcreteTypeDictionary)
        {
            var myScope = new ComponentInstanceScope() { Identifiers = parentScope.Identifiers.Add(comp.Identifier) };
            var myFieldList = new List<FieldInfo>();
            var myLocalFieldDictionary = new Dictionary<MM.Identifier, FieldInfo>();
            var myFieldDictionary = new Dictionary<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>>();

            var type = mmAccessTypeToConcreteTypeDictionary.Resolve(comp.Type);

            var fieldWithValue = type.Fields.Zip(comp.FieldValues, (field, initialValue)
                                                                       =>
                                                                       new Tuple
                                                                       <MMDeclarations.FieldDeclaration, MMConfigurations.ValueArray>(
                                                                       field, initialValue));
            foreach (var tuple in fieldWithValue)
            {
                var fieldDecl = tuple.Item1;
                var fieldInitialValue = tuple.Item2;
                var fieldInfo = new FieldInfo
                {
                    Fieldname = fieldDecl.Identifier,
                    AffectedComponentScope = myScope,
                    InitialValues = fieldInitialValue,
                    FieldDeclaration = fieldDecl
                };
                myFieldList.Add(fieldInfo);
                myLocalFieldDictionary.Add(fieldDecl.Identifier, fieldInfo);
            };

            myFieldDictionary.Add(myScope, myLocalFieldDictionary.ToImmutableDictionary());

            foreach (var subcomp in comp.SubComponents)
            {
                var newTuple = ExtractFields(subcomp, myScope, mmAccessTypeToConcreteTypeDictionary);
                myFieldList.AddRange(newTuple.MmFieldList);
                foreach (var dictionaryEntry in newTuple.MmFieldDictionary)
                    myFieldDictionary.Add(dictionaryEntry.Key, dictionaryEntry.Value);
            };
            return new ExtractFieldsTuple
            {
                MmFieldList = myFieldList.ToImmutableArray(),
                MmFieldDictionary = myFieldDictionary.ToImmutableDictionary()
            };
        }

        public static ExtractFieldsTuple ExtractFields(MM.MetamodelConfiguration mm,
                                                       MM.MetamodelResolver mmAccessTypeToConcreteTypeDictionary)
        {
            var myFieldList = new List<FieldInfo>();
            var myFieldDictionary = new Dictionary<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>>();
            foreach (MMConfigurations.Partition part in mm.Partitions)
            {
                var scope = new ComponentInstanceScope() { Identifiers = ImmutableArray<MM.Identifier>.Empty };
                var newTuple = ExtractFields(part.Component, scope, mmAccessTypeToConcreteTypeDictionary);
                myFieldList.AddRange(newTuple.MmFieldList);
                foreach (var dictionaryEntry in newTuple.MmFieldDictionary)
                    myFieldDictionary.Add(dictionaryEntry.Key, dictionaryEntry.Value);
            }
            return new ExtractFieldsTuple
            {
                MmFieldList = myFieldList.ToImmutableArray(),
                MmFieldDictionary = myFieldDictionary.ToImmutableDictionary()
            };
        }

        internal struct ExtractFieldsTuple
        {
            public ImmutableDictionary<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>> MmFieldDictionary;
            public ImmutableArray<FieldInfo> MmFieldList;
        }
    }

    internal class MetamodelExpressionToPromelaExpression : MM.MetamodelVisitor<PrExpression>
    {
        public MetamodelExpressionToPromelaExpression(MetamodelToPromela commonKnowledge, ComponentInstanceScope currentComponent)
        {
            CommonKnowledge = commonKnowledge;
            CurrentComponent = currentComponent;
        }

        private MetamodelToPromela CommonKnowledge { get; set; }
        private ComponentInstanceScope CurrentComponent { get; set; }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.BooleanLiteral" />.
        /// </summary>
        /// <param name="booleanLiteral">The <see cref="MMExpressions.BooleanLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitBooleanLiteral(MMExpressions.BooleanLiteral booleanLiteral)
        {
            Argument.NotNull(booleanLiteral, () => booleanLiteral);
            return new PrExpressions.BooleanLiteral(booleanLiteral.Value);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.IntegerLiteral" />.
        /// </summary>
        /// <param name="integerLiteral">The <see cref="MMExpressions.IntegerLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitIntegerLiteral(MMExpressions.IntegerLiteral integerLiteral)
        {
            Argument.NotNull(integerLiteral, () => integerLiteral);
            return new PrExpressions.NumberLiteral(integerLiteral.Value);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.DecimalLiteral" />.
        /// </summary>
        /// <param name="decimalLiteral">The <see cref="MMExpressions.DecimalLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitDecimalLiteral(MMExpressions.DecimalLiteral decimalLiteral)
        {
            Argument.NotNull(decimalLiteral, () => decimalLiteral);
            throw new NotImplementedException();
        }

        private PromelaBinaryOperator MmBinOperatorToPrBinOperator(MMExpressions.BinaryOperator @operator)
        {
            switch (@operator)
            {
                case MMExpressions.BinaryOperator.Add:
                    return PromelaBinaryOperator.Add;
                case MMExpressions.BinaryOperator.Subtract:
                    return PromelaBinaryOperator.Min;
                case MMExpressions.BinaryOperator.Multiply:
                    return PromelaBinaryOperator.Mul;
                case MMExpressions.BinaryOperator.Divide:
                    return PromelaBinaryOperator.Div;
                case MMExpressions.BinaryOperator.Modulo:
                    return PromelaBinaryOperator.Mod;
                case MMExpressions.BinaryOperator.LogicalAnd:
                    return PromelaBinaryOperator.And;
                case MMExpressions.BinaryOperator.LogicalOr:
                    return PromelaBinaryOperator.Or;
                case MMExpressions.BinaryOperator.Equals:
                    return PromelaBinaryOperator.Eq;
                case MMExpressions.BinaryOperator.NotEquals:
                    return PromelaBinaryOperator.Neq;
                case MMExpressions.BinaryOperator.LessThan:
                    return PromelaBinaryOperator.Lt;
                case MMExpressions.BinaryOperator.LessThanOrEqual:
                    return PromelaBinaryOperator.Le;
                case MMExpressions.BinaryOperator.GreaterThan:
                    return PromelaBinaryOperator.Gt;
                case MMExpressions.BinaryOperator.GreaterThanOrEqual:
                    return PromelaBinaryOperator.Ge;
                default:
                    throw new NotImplementedException();
            }
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="MMExpressions.BinaryExpression" /> instance that should be visited.</param>
        public override PrExpression VisitBinaryExpression(MMExpressions.BinaryExpression binaryExpression)
        {
            Argument.NotNull(binaryExpression, () => binaryExpression);
            var left = binaryExpression.Left.Accept(this);
            var @operator = MmBinOperatorToPrBinOperator(binaryExpression.Operator);
            var right = binaryExpression.Right.Accept(this);
            return new PrExpressions.BinaryExpression(left, @operator, right);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="MMExpressions.UnaryExpression" /> instance that should be visited.</param>
        public override PrExpression VisitUnaryExpression(MMExpressions.UnaryExpression unaryExpression)
        {
            Argument.NotNull(unaryExpression, () => unaryExpression);
            var operand = unaryExpression.Operand.Accept(this);
            switch (unaryExpression.Operator)
            {
                case MMExpressions.UnaryOperator.LogicalNot:
                    return new PrExpressions.UnaryExpression(operand, PromelaUnaryOperator.Not);
                case MMExpressions.UnaryOperator.Minus:
                    return new PrExpressions.UnaryExpression(operand, PromelaUnaryOperator.Neg);
                default:
                    throw new NotImplementedException();
            }
        }

        public PrExpressions.VariableReferenceExpression ConvertFieldAccessExpression(
            MMExpressions.FieldAccessExpression fieldAccessExpression)
        {
            Argument.NotNull(fieldAccessExpression, () => fieldAccessExpression);
            var fieldDeclaration = CommonKnowledge.MmAccessTypeToConcreteTypeDictionary.Resolve(fieldAccessExpression.Field);
            var fieldInfo = CommonKnowledge.MmFieldDictionary[CurrentComponent][fieldDeclaration.Identifier];
            var refName = fieldInfo.GetName();
            return new PrExpressions.VariableReferenceExpression(refName, null, null);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.FieldAccessExpression" />.
        /// </summary>
        /// <param name="fieldAccessExpression">The <see cref="MMExpressions.FieldAccessExpression" /> instance that should be visited.</param>
        public override PrExpression VisitFieldAccessExpression(MMExpressions.FieldAccessExpression fieldAccessExpression)
        {
            Argument.NotNull(fieldAccessExpression, () => fieldAccessExpression);
            return ConvertFieldAccessExpression(fieldAccessExpression);
        }
    }

    #endregion

    #region Statements

    internal class MetamodelStatementToPromelaStatement : MM.MetamodelVisitor<PrStatement>
    {
        public MetamodelStatementToPromelaStatement(MetamodelToPromela commonKnowledge, ComponentInstanceScope currentComponent)
        {
            CommonKnowledge = commonKnowledge;
            CurrentComponent = currentComponent;
        }

        private MetamodelToPromela CommonKnowledge { get; set; }
        private ComponentInstanceScope CurrentComponent { get; set; }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.EmptyStatement" />.
        /// </summary>
        /// <param name="emptyStatement">The <see cref="MMStatements.EmptyStatement" /> instance that should be visited.</param>
        public override PrStatement VisitEmptyStatement(MMStatements.EmptyStatement emptyStatement)
        {
            Argument.NotNull(emptyStatement, () => emptyStatement);
            return new PrStatements.SkipStatement();
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.BlockStatement" />.
        /// </summary>
        /// <param name="blockStatement">The <see cref="MMStatements.BlockStatement" /> instance that should be visited.</param>
        public override PrStatement VisitBlockStatement(MMStatements.BlockStatement blockStatement)
        {
            Argument.NotNull(blockStatement, () => blockStatement);
            var substatements = blockStatement.Statements.Select(statement => statement.Accept(this)).ToImmutableArray();
            return new PrStatements.SimpleBlockStatement(substatements);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="MMStatements.ReturnStatement" /> instance that should be visited.</param>
        public override PrStatement VisitReturnStatement(MMStatements.ReturnStatement returnStatement)
        {
            Argument.NotNull(returnStatement, () => returnStatement);
            throw new NotImplementedException();
        }

        /// <summary>
        ///   Converts an element of type <see cref="MMStatements.GuardedCommandClause" />.
        /// </summary>
        /// <param name="guardedCommandClause">The <see cref="MMStatements.GuardedCommandClause" /> instance that should be converted.</param>
        public PrStatements.GuardedCommandClause ConvertGuardedCommandClause(MMStatements.GuardedCommandClause guardedCommandClause)
        {
            Argument.NotNull(guardedCommandClause, () => guardedCommandClause);
            var guard = guardedCommandClause.Guard.Accept(CommonKnowledge.GetExpressionVisitor(CurrentComponent));
            var statement = guardedCommandClause.Statement.Accept(this);
            return new PrStatements.GuardedCommandExpressionClause(guard, statement);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.GuardedCommandStatement" />.
        /// </summary>
        /// <param name="guardedCommandStatement">
        ///   The <see cref="MMStatements.GuardedCommandStatement" /> instance that should be
        ///   visited.
        /// </param>
        public override PrStatement VisitGuardedCommandStatement(MMStatements.GuardedCommandStatement guardedCommandStatement)
        {
            Argument.NotNull(guardedCommandStatement, () => guardedCommandStatement);
            var clauses = guardedCommandStatement.Clauses.Select(ConvertGuardedCommandClause).ToImmutableArray();
            return new PrStatements.GuardedCommandSelectionStatement(clauses);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="MMStatements.AssignmentStatement" /> instance that should be visited.</param>
        public override PrStatement VisitAssignmentStatement(MMStatements.AssignmentStatement assignmentStatement)
        {
            Argument.NotNull(assignmentStatement, () => assignmentStatement);
            // Be careful: http://stackoverflow.com/questions/983030/type-checking-typeof-gettype-or-is
            var stateVar = assignmentStatement.Left as MMExpressions.FieldAccessExpression;

            if (stateVar == null)
            {
                //setter is called or variable is somewhere in the hierarchie.
                throw new NotImplementedException();
            }
            var newVarRef = CommonKnowledge.GetExpressionVisitor(CurrentComponent).ConvertFieldAccessExpression(stateVar);

            var rightExpression = assignmentStatement.Right.Accept(CommonKnowledge.GetExpressionVisitor(CurrentComponent));

            return new PrStatements.AssignmentStatement(newVarRef, rightExpression);
        }
    }

    #endregion
}