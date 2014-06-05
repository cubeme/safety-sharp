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
    using PrFormula = SafetySharp.Modelchecking.Promela.Formula;
    using MMFormulae = SafetySharp.Formulas;
    using Metamodel.Types;
    using Microsoft.CodeAnalysis;
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

        public override bool Equals(Object obj)
        {
            return obj is ComponentInstanceScope && this == (ComponentInstanceScope)obj;
        }

        public override int GetHashCode()
        {
            var hashCode = 1;
            foreach (var identifier in Identifiers)
            {
                hashCode = 31 * hashCode + (identifier.GetHashCode());
            }
            return hashCode;
        }

        public static bool operator ==(ComponentInstanceScope x, ComponentInstanceScope y)
        {
            return x.Identifiers.SequenceEqual(y.Identifiers);
        }

        public static bool operator !=(ComponentInstanceScope x, ComponentInstanceScope y)
        {
            return !(x == y);
        }
    };

    internal struct FieldInfo
    {
        //internal ImmutableArray<MM.Identifier> ComponentInstanceNames;
        internal ComponentInstanceScope AffectedComponentScope;
        internal MMDeclarations.FieldDeclaration FieldDeclaration;
        internal MM.Identifier Fieldname;
        internal MMConfigurations.FieldConfiguration InitialValues; // TODO DICTIONARY REFACTORING

        internal string GetName()
        {
			//TODO: Add C in the name for component and V for variables to omit clashes
			return String.Format("C{0}_V{1}", String.Join("_C", AffectedComponentScope.Identifiers), Fieldname.Name);
        }

        public override bool Equals(Object obj)
        {
            return obj is FieldInfo && this == (FieldInfo)obj;
        }

        public override int GetHashCode()
        {
            return AffectedComponentScope.GetHashCode()
                   ^ FieldDeclaration.GetHashCode()
                   ^ Fieldname.GetHashCode()
                   ^ InitialValues.GetHashCode();
        }

        public static bool operator ==(FieldInfo x, FieldInfo y)
        {
            return x.AffectedComponentScope == y.AffectedComponentScope
                && x.FieldDeclaration == y.FieldDeclaration
                && x.Fieldname == y.Fieldname
				   && x.InitialValues == y.InitialValues;
        }

        public static bool operator !=(FieldInfo x, FieldInfo y)
        {
            return !(x == y);
        }
    }

    internal struct ComponentConfigurationUpdateMethod
    {
        internal MMConfigurations.ComponentConfiguration AffectedComponentConfiguration;
        internal ComponentInstanceScope AffectedComponentScope;
        internal MMStatements.Statement UpdateMethod;

        public override bool Equals(Object obj)
        {
            return obj is ComponentConfigurationUpdateMethod && this == (ComponentConfigurationUpdateMethod)obj;
        }

        public override int GetHashCode()
        {
            return AffectedComponentConfiguration.GetHashCode()
                   ^ AffectedComponentScope.GetHashCode()
                   ^ UpdateMethod.GetHashCode();
        }

        public static bool operator ==(ComponentConfigurationUpdateMethod x, ComponentConfigurationUpdateMethod y)
        {
            return x.AffectedComponentConfiguration == y.AffectedComponentConfiguration
                && x.AffectedComponentScope == y.AffectedComponentScope
                && x.UpdateMethod == y.UpdateMethod;
        }

        public static bool operator !=(ComponentConfigurationUpdateMethod x, ComponentConfigurationUpdateMethod y)
        {
            return !(x == y);
        }
    }
    
    internal class MetamodelToPromela
    {
        public readonly MM.MetamodelConfiguration Mm;
        public readonly MM.MetamodelResolver MmAccessTypeToConcreteTypeDictionary;

        public readonly ImmutableArray<FieldInfo> MmFieldList;

        public readonly IImmutableDictionary<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>> MmFieldDictionary;

        public readonly IImmutableDictionary<MMConfigurations.ComponentConfiguration, ComponentInstanceScope> MmConfigurationToScope;

        public MetamodelToPromela(MM.MetamodelConfiguration mm, MM.MetamodelResolver metamodelResolver)
        {
            Mm = mm;
            MmAccessTypeToConcreteTypeDictionary = metamodelResolver;
            var extractedFields = ExtractFieldsAndConfiguration(Mm, MmAccessTypeToConcreteTypeDictionary);
            MmFieldList = extractedFields.MmFieldList;
            MmFieldDictionary = extractedFields.MmFieldDictionary;
            MmConfigurationToScope = extractedFields.MmConfigurationToScope;
        }
        
        public MetamodelExpressionToPromelaExpression GetExpressionVisitor(ComponentInstanceScope currentComponent)
        {
            return new MetamodelExpressionToPromelaExpression(this, currentComponent);
        }

        public MetamodelStatementToPromelaStatement GetStatementVisitor(ComponentInstanceScope currentComponent)
        {
            return new MetamodelStatementToPromelaStatement(this, currentComponent);
        }
        public MetamodelFormulaToPromelaFormula GetFormulaVisitor()
        {
            return new MetamodelFormulaToPromelaFormula(this);
        }

        //this is the top level element of a meta model
        public PromelaFile ConvertMetaModelConfiguration()
        {
            var fieldDeclarations = GenerateFieldDeclarations();
            var globalFieldModule = new PromelaGlobalVarsAndChans(fieldDeclarations);

            var fieldInitialisations = GenerateFieldInitialisations();
            var systemSteps = Mm.Partitions.SelectMany(partition =>
														   ImmutableArray.Create(GenerateUpdateStatements(partition, MmFieldList),
																				 GenerateBindingExecutionStatements(partition, MmFieldList)));
            var systemStepsBlock = new PrStatements.SimpleBlockStatement(systemSteps.AsImmutable());

            var systemLoop = PromelaHelpers.CoverStatementInEndlessLoop(systemStepsBlock);

            var code = fieldInitialisations.Add(systemLoop);
            var systemProctype = new Proctype(true, "System", code);

            var promelaFile = new PromelaFile(ImmutableArray.Create<PromelaModule>(globalFieldModule, systemProctype));

            return promelaFile;
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

        public PrExpressions.ConstExpression ConvertObject(object mmValue, TypeSymbol type)
        {
            if (type is VoidType)
                throw new NotImplementedException();
            if (type is BooleanType)
            {
                var value = (bool)mmValue;
                return new PrExpressions.BooleanLiteral(value);
            }
            if (type is IntegerType)
            {
                var value = (int)mmValue;
                return new PrExpressions.NumberLiteral(value);
            }
            if (type is DecimalType)
                throw new NotImplementedException();
            if (type is InterfaceType)
                throw new NotImplementedException();
            throw new NotImplementedException();
        }

        public ImmutableArray<PrStatements.DeclarationStatement> GenerateFieldDeclarations()
        {
            var statements = MmFieldList.Select(field =>
            {
                var type = field.FieldDeclaration.Type;
                var name = field.GetName();
                var declStatement = new PrStatements.DeclarationStatement(ConvertType(type), name, 1, null);
                return  declStatement;
            });
            return statements.ToImmutableArray();
        }
        public ImmutableArray<PrStatement> GenerateFieldInitialisations()
        {
            var statements = MmFieldList.Select(field =>
            {
                var type = field.FieldDeclaration.Type;
                var name = field.GetName();
                var initialvalueClauses = field.InitialValues.InitialValues.Select(// TODO DICTIONARY REFACTORING
                    value =>
                    {
                        var prValue = ConvertObject(value, type);
                        var clause = new PrStatements.GuardedCommandExpressionClause(PromelaHelpers.ConstTrueExpression(),
                                                                                     PromelaHelpers.SimpleFieldAssignment(name, prValue));
                        return (PrStatements.GuardedCommandClause)clause;
                    });
                var initialValueStatement = new PrStatements.GuardedCommandSelectionStatement(initialvalueClauses.ToImmutableArray());
                return (PrStatement) initialValueStatement ;
            });
            return statements.ToImmutableArray();
        }

        public ImmutableArray<ComponentConfigurationUpdateMethod> CollectUpdateMethodsInOrder(MMConfigurations.Partition partition)
        {
            var scope = new ComponentInstanceScope { Identifiers = ImmutableArray<MM.Identifier>.Empty };
            return CollectUpdateMethodsInOrder(partition.Component, scope);
        }

		public ImmutableArray<ComponentConfigurationUpdateMethod> CollectUpdateMethodsInOrder(MMConfigurations.ComponentConfiguration component,
																							  ComponentInstanceScope parentScope)
        {
			var updateMethods = ImmutableArray.CreateBuilder<ComponentConfigurationUpdateMethod>(32);
			var scope = new ComponentInstanceScope { Identifiers = parentScope.Identifiers.Add(component.Identifier) };
            var updateMethod = new ComponentConfigurationUpdateMethod
            {
                AffectedComponentScope = scope,
                AffectedComponentConfiguration = component,
                UpdateMethod = component.Declaration.UpdateMethod.Body
            };

            updateMethods.Add(updateMethod);
			updateMethods.AddRange(component.SubComponents.SelectMany(c => CollectUpdateMethodsInOrder(c, scope)));

            return updateMethods.ToImmutableArray();
        }

        //TODO: Bring the Update Statements in the correct order
        public PrStatement GenerateUpdateStatements(MMConfigurations.Partition partition, ImmutableArray<FieldInfo> fields)
        {
            var promelaUpdateStatements = new List<PrStatement>();
            var updateMethods = CollectUpdateMethodsInOrder(partition);
            foreach (var componentConfigurationUpdateMethod in updateMethods)
            {
				var visitor = GetStatementVisitor(componentConfigurationUpdateMethod.AffectedComponentScope);
                var promelaUpdateStatement = componentConfigurationUpdateMethod.UpdateMethod.Accept(visitor);
                promelaUpdateStatements.Add(promelaUpdateStatement);
            }
            return new PrStatements.SimpleBlockStatement(promelaUpdateStatements.AsImmutable());
        }

        public PrStatement GenerateBindingExecutionStatements(MMConfigurations.Partition partition, ImmutableArray<FieldInfo> fields)
        {
            //throw new NotImplementedException();
            //TODO: Bindings
            return new PrStatements.SkipStatement();
        }


        //TODO: Export in own class (something like augmented model, information collector, model walker, model navigation information,...)
        public static ExtractionTuple ExtractFieldsAndConfiguration(MMConfigurations.ComponentConfiguration comp,
                                                       ComponentInstanceScope parentScope,
                                                       MM.MetamodelResolver mmAccessTypeToConcreteTypeDictionary)
        {
			var myScope = new ComponentInstanceScope { Identifiers = parentScope.Identifiers.Add(comp.Identifier) };
			var myFieldList = ImmutableArray.CreateBuilder<FieldInfo>();
			var myLocalFieldDictionary = ImmutableDictionary.CreateBuilder<MM.Identifier, FieldInfo>();
            var myFieldDictionary = ImmutableDictionary.CreateBuilder<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>>();
            var myComponentConfigurationDictionary =
                ImmutableDictionary.CreateBuilder<MMConfigurations.ComponentConfiguration, ComponentInstanceScope>();

            var type = comp.Declaration;

			for (var i = 0; i < type.Fields.Length; ++i)
            {
				var fieldDecl = type.Fields[i];
				var fieldInitialValue = comp.Fields.Skip(i).Single().Value; // TODO DICTIONARY REFACTORING
                var fieldInfo = new FieldInfo
                {
                    Fieldname = fieldDecl.Identifier,
                    AffectedComponentScope = myScope,
                    InitialValues = fieldInitialValue,
                    FieldDeclaration = fieldDecl
                };
                myFieldList.Add(fieldInfo);
                myLocalFieldDictionary.Add(fieldDecl.Identifier, fieldInfo);
			}

            myFieldDictionary.Add(myScope, myLocalFieldDictionary.ToImmutableDictionary());
            myComponentConfigurationDictionary.Add(comp, myScope);

            foreach (var subcomp in comp.SubComponents)
            {
                var newTuple = ExtractFieldsAndConfiguration(subcomp, myScope, mmAccessTypeToConcreteTypeDictionary);
                myFieldList.AddRange(newTuple.MmFieldList);
                foreach (var dictionaryEntry in newTuple.MmFieldDictionary)
                    myFieldDictionary.Add(dictionaryEntry.Key, dictionaryEntry.Value);
                foreach (var dictionaryEntry in newTuple.MmConfigurationToScope)
                    myComponentConfigurationDictionary.Add(dictionaryEntry.Key, dictionaryEntry.Value);


            }
            return new ExtractionTuple
            {
                MmFieldList = myFieldList.ToImmutableArray(),
                MmFieldDictionary = myFieldDictionary.ToImmutableDictionary(),
                MmConfigurationToScope = myComponentConfigurationDictionary.ToImmutableDictionary()
            };
        }

        public static ExtractionTuple ExtractFieldsAndConfiguration(MM.MetamodelConfiguration mm,
                                                       MM.MetamodelResolver mmAccessTypeToConcreteTypeDictionary)
        {
            var myFieldList = ImmutableArray.CreateBuilder<FieldInfo>();
            var myFieldDictionary = ImmutableDictionary.CreateBuilder<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>>();
            var myComponentConfigurationDictionary =
                ImmutableDictionary.CreateBuilder<MMConfigurations.ComponentConfiguration, ComponentInstanceScope>();
            foreach (MMConfigurations.Partition part in mm.Partitions)
            {
                var scope = new ComponentInstanceScope { Identifiers = ImmutableArray<MM.Identifier>.Empty };
                var newTuple = ExtractFieldsAndConfiguration(part.Component, scope, mmAccessTypeToConcreteTypeDictionary);
                myFieldList.AddRange(newTuple.MmFieldList);
                foreach (var dictionaryEntry in newTuple.MmFieldDictionary)
                    myFieldDictionary.Add(dictionaryEntry.Key, dictionaryEntry.Value);
                foreach (var dictionaryEntry in newTuple.MmConfigurationToScope)
                    myComponentConfigurationDictionary.Add(dictionaryEntry.Key, dictionaryEntry.Value);
            }
            return new ExtractionTuple
            {
                MmFieldList = myFieldList.ToImmutableArray(),
                MmFieldDictionary = myFieldDictionary.ToImmutableDictionary(),
                MmConfigurationToScope = myComponentConfigurationDictionary.ToImmutableDictionary()
            };
        }


        internal struct ExtractionTuple
        {
            public ImmutableDictionary<ComponentInstanceScope, ImmutableDictionary<MM.Identifier, FieldInfo>> MmFieldDictionary;
            public ImmutableDictionary<MMConfigurations.ComponentConfiguration, ComponentInstanceScope> MmConfigurationToScope;
            public ImmutableArray<FieldInfo> MmFieldList;
        }

        internal LtlFormulaModule ConvertFormula(MMFormulae.Formula forumula)
        {
            var formulaVistior = GetFormulaVisitor();
            var promelaformula = forumula.Accept(formulaVistior);
            return new LtlFormulaModule(null, promelaformula);
        }
    }

    internal class MetamodelFormulaToPromelaFormula : MMFormulae.FormulaVisitor<PrFormula.PromelaFormula>
    {
        private readonly MetamodelToPromela _commonKnowledge;

        public MetamodelFormulaToPromelaFormula(MetamodelToPromela commonKnowledge)
        {
            _commonKnowledge = commonKnowledge;
        }

        /// <summary>
        ///     Visits an element of type <see cref="MMFormulae.StateFormula" />.
        /// </summary>
        /// <param name="expressionFormula">The <see cref="MMFormulae.StateFormula" /> instance that should be visited.</param>
        public override PrFormula.PromelaFormula VisitStateFormula(MMFormulae.StateFormula expressionFormula)
        {
            Requires.NotNull(expressionFormula, () => expressionFormula);

            var scope = _commonKnowledge.MmConfigurationToScope[/* TODO: REMOVED ASSOCIATED COMPONENT */null];
            var expressionVisitor = _commonKnowledge.GetExpressionVisitor(scope);
            var promelaFormula = expressionFormula.Expression.Accept(expressionVisitor);
            return new PrFormula.PropositionalStateFormula(promelaFormula);

        }

        /// <summary>
        ///     Visits an element of type <see cref="MMFormulae.BinaryFormula" />.
        /// </summary>
        /// <param name="binaryFormula">The <see cref="MMFormulae.BinaryFormula" /> instance that should be visited.</param>
        public override PrFormula.PromelaFormula VisitBinaryFormula(MMFormulae.BinaryFormula binaryFormula)
        {
            Requires.NotNull(binaryFormula, () => binaryFormula);
            var left = binaryFormula.Left.Accept(this);
            var right = binaryFormula.Right.Accept(this);
            PromelaBinaryFormulaOperator @operator;

            switch (binaryFormula.Operator)
            {
                case MMFormulae.BinaryTemporalOperator.And:
                    @operator = PromelaBinaryFormulaOperator.And;
                    break;
                case MMFormulae.BinaryTemporalOperator.Or:
                    @operator = PromelaBinaryFormulaOperator.Or;
                    break;
                case MMFormulae.BinaryTemporalOperator.Implication:
                    @operator = PromelaBinaryFormulaOperator.Implies;
                    break;
                case MMFormulae.BinaryTemporalOperator.Equivalence:
                    @operator = PromelaBinaryFormulaOperator.Equals;
                    break;
                case MMFormulae.BinaryTemporalOperator.Until:
                    @operator = PromelaBinaryFormulaOperator.Until;
                    break;
                default:
                    throw new NotImplementedException();
            }

            return new PrFormula.BinaryFormula(left,@operator,right);

        }

        /// <summary>
        ///     Visits an element of type <see cref="MMFormulae.UnaryFormula" />.
        /// </summary>
        /// <param name="unaryFormula">The <see cref="MMFormulae.UnaryFormula" /> instance that should be visited.</param>
        public override PrFormula.PromelaFormula VisitUnaryFormula(MMFormulae.UnaryFormula unaryFormula)
        {
            Requires.NotNull(unaryFormula, () => unaryFormula);
            var operand = unaryFormula.Operand.Accept(this);
            PromelaUnaryFormulaOperator @operator;
            
            switch (unaryFormula.Operator)
            {
                case MMFormulae.UnaryTemporalOperator.Not:
                    @operator = PromelaUnaryFormulaOperator.Not;
                    break;
                case MMFormulae.UnaryTemporalOperator.Next:
                    throw new NotImplementedException("UnaryTemporalOperator.Next not yet implemented in Promela. There are diverse problems with it. Read http://spinroot.com/spin/Man/ltl.html");
                case MMFormulae.UnaryTemporalOperator.Finally:
                    @operator = PromelaUnaryFormulaOperator.Eventually;
                    break;
                case MMFormulae.UnaryTemporalOperator.Globally:
                    @operator = PromelaUnaryFormulaOperator.Always;
                    break;

                default:
                    throw new NotImplementedException();
            }

            return new PrFormula.UnaryFormula(operand, @operator);
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
            Requires.NotNull(booleanLiteral, () => booleanLiteral);
            return new PrExpressions.BooleanLiteral(booleanLiteral.Value);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.IntegerLiteral" />.
        /// </summary>
        /// <param name="integerLiteral">The <see cref="MMExpressions.IntegerLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitIntegerLiteral(MMExpressions.IntegerLiteral integerLiteral)
        {
            Requires.NotNull(integerLiteral, () => integerLiteral);
            return new PrExpressions.NumberLiteral(integerLiteral.Value);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMExpressions.DecimalLiteral" />.
        /// </summary>
        /// <param name="decimalLiteral">The <see cref="MMExpressions.DecimalLiteral" /> instance that should be visited.</param>
        public override PrExpression VisitDecimalLiteral(MMExpressions.DecimalLiteral decimalLiteral)
        {
            Requires.NotNull(decimalLiteral, () => decimalLiteral);
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
            Requires.NotNull(binaryExpression, () => binaryExpression);
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
            Requires.NotNull(unaryExpression, () => unaryExpression);
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
            Requires.NotNull(fieldAccessExpression, () => fieldAccessExpression);
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
            Requires.NotNull(fieldAccessExpression, () => fieldAccessExpression);
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
            Requires.NotNull(emptyStatement, () => emptyStatement);
            return new PrStatements.SkipStatement();
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.BlockStatement" />.
        /// </summary>
        /// <param name="blockStatement">The <see cref="MMStatements.BlockStatement" /> instance that should be visited.</param>
        public override PrStatement VisitBlockStatement(MMStatements.BlockStatement blockStatement)
        {
            Requires.NotNull(blockStatement, () => blockStatement);
            var substatements = blockStatement.Statements.Select(statement => statement.Accept(this)).ToImmutableArray();
            return new PrStatements.SimpleBlockStatement(substatements);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="MMStatements.ReturnStatement" /> instance that should be visited.</param>
        public override PrStatement VisitReturnStatement(MMStatements.ReturnStatement returnStatement)
        {
            Requires.NotNull(returnStatement, () => returnStatement);
            throw new NotImplementedException();
        }

        /// <summary>
        ///   Converts an element of type <see cref="MMStatements.GuardedCommandClause" />.
        /// </summary>
        /// <param name="guardedCommandClause">The <see cref="MMStatements.GuardedCommandClause" /> instance that should be converted.</param>
        public PrStatements.GuardedCommandClause ConvertGuardedCommandClause(MMStatements.GuardedCommandClause guardedCommandClause)
        {
            Requires.NotNull(guardedCommandClause, () => guardedCommandClause);
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
            Requires.NotNull(guardedCommandStatement, () => guardedCommandStatement);
            var clauses = guardedCommandStatement.Clauses.Select(ConvertGuardedCommandClause).ToImmutableArray();
            return new PrStatements.GuardedCommandSelectionStatement(clauses);
        }

        /// <summary>
        ///   Visits an element of type <see cref="MMStatements.AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="MMStatements.AssignmentStatement" /> instance that should be visited.</param>
        public override PrStatement VisitAssignmentStatement(MMStatements.AssignmentStatement assignmentStatement)
        {
            Requires.NotNull(assignmentStatement, () => assignmentStatement);
            // Be careful: http://stackoverflow.com/questions/983030/type-checking-typeof-gettype-or-is
            var stateVar = assignmentStatement.Left as MMExpressions.FieldAccessExpression;

            if (stateVar == null)
            {
				//setter is called or variable is somewhere in the hierarchy.
                throw new NotImplementedException();
            }
            var newVarRef = CommonKnowledge.GetExpressionVisitor(CurrentComponent).ConvertFieldAccessExpression(stateVar);

            var rightExpression = assignmentStatement.Right.Accept(CommonKnowledge.GetExpressionVisitor(CurrentComponent));

            return new PrStatements.AssignmentStatement(newVarRef, rightExpression);
        }
    }

    #endregion
}