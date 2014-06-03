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
{
    using System;
    using SafetySharp.Modelchecking.NuXmv.Expressions;
    using SafetySharp.Modelchecking.NuXmv.FSM;
    using SafetySharp.Modelchecking.NuXmv.SimpleTypeSpecifiers;
    using SafetySharp.Modelchecking.NuXmv.Specifications;
    using SafetySharp.Modelchecking.NuXmv.Types;
    using Utilities;

    internal class NuXmvModelWriter : NuXmvVisitor
    {
        public NuXmvModelWriter()
        {
            CodeWriter = new CodeWriter();
        }

        public NuXmvModelWriter(bool skipHeader)
        {
            if (skipHeader)
            {
                CodeWriter = new CodeWriter(null);
            }
            else
            {
                CodeWriter = new CodeWriter();
            }
        }

        public readonly CodeWriter CodeWriter;


        /// <summary>
        ///     Visits an element of type <see cref="Identifier" />.
        /// </summary>
        /// <param name="identifier">The <see cref="Identifier" /> instance that should be visited.</param>
        public override void VisitIdentifier(Identifier identifier)
        {
            Argument.NotNull(identifier, () => identifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="NameComplexIdentifier" />.
        /// </summary>
        /// <param name="nameComplexIdentifier">The <see cref="NameComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitNameComplexIdentifier(NameComplexIdentifier nameComplexIdentifier)
        {
            Argument.NotNull(nameComplexIdentifier, () => nameComplexIdentifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="NestedComplexIdentifier" />.
        /// </summary>
        /// <param name="nestedComplexIdentifier">The <see cref="NestedComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitNestedComplexIdentifier(NestedComplexIdentifier nestedComplexIdentifier)
        {
            Argument.NotNull(nestedComplexIdentifier, () => nestedComplexIdentifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="ArrayAccessComplexIdentifier" />.
        /// </summary>
        /// <param name="arrayAccessComplexIdentifier">The <see cref="ArrayAccessComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitArrayAccessComplexIdentifier(ArrayAccessComplexIdentifier arrayAccessComplexIdentifier)
        {
            Argument.NotNull(arrayAccessComplexIdentifier, () => arrayAccessComplexIdentifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SelfComplexIdentifier" />.
        /// </summary>
        /// <param name="selfComplexIdentifier">The <see cref="SelfComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitSelfComplexIdentifier(SelfComplexIdentifier selfComplexIdentifier)
        {
            Argument.NotNull(selfComplexIdentifier, () => selfComplexIdentifier);
            throw new NotImplementedException();
        }











        /// <summary>
        ///     Visits an element of type <see cref="BooleanType" />.
        /// </summary>
        /// <param name="booleanType">The <see cref="BooleanType" /> instance that should be visited.</param>
        public override void VisitBooleanType(BooleanType booleanType)
        {
            Argument.NotNull(booleanType, () => booleanType);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="EnumerationType" />.
        /// </summary>
        /// <param name="enumerationType">The <see cref="EnumerationType" /> instance that should be visited.</param>
        public override void VisitEnumerationType(EnumerationType enumerationType)
        {
            Argument.NotNull(enumerationType, () => enumerationType);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnsignedWordType" />.
        /// </summary>
        /// <param name="unsignedWordType">The <see cref="UnsignedWordType" /> instance that should be visited.</param>
        public override void VisitUnsignedWordType(UnsignedWordType unsignedWordType)
        {
            Argument.NotNull(unsignedWordType, () => unsignedWordType);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SignedWordType" />.
        /// </summary>
        /// <param name="signedWordType">The <see cref="SignedWordType" /> instance that should be visited.</param>
        public override void VisitSignedWordType(SignedWordType signedWordType)
        {
            Argument.NotNull(signedWordType, () => signedWordType);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerType" />.
        /// </summary>
        /// <param name="integerType">The <see cref="IntegerType" /> instance that should be visited.</param>
        public override void VisitIntegerType(IntegerType integerType)
        {
            Argument.NotNull(integerType, () => integerType);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="RealType" />.
        /// </summary>
        /// <param name="realType">The <see cref="RealType" /> instance that should be visited.</param>
        public override void VisitRealType(RealType realType)
        {
            Argument.NotNull(realType, () => realType);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="ArrayType" />.
        /// </summary>
        /// <param name="arrayType">The <see cref="ArrayType" /> instance that should be visited.</param>
        public override void VisitArrayType(ArrayType arrayType)
        {
            Argument.NotNull(arrayType, () => arrayType);
            throw new NotImplementedException();
        }











        /// <summary>
        ///     Visits an element of type <see cref="BooleanTypeSpecifier" />.
        /// </summary>
        /// <param name="booleanTypeSpecifier">The <see cref="BooleanTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitBooleanTypeSpecifier(BooleanTypeSpecifier booleanTypeSpecifier)
        {
            Argument.NotNull(booleanTypeSpecifier, () => booleanTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnsignedWordTypeSpecifier" />.
        /// </summary>
        /// <param name="unsignedWordTypeSpecifier">The <see cref="UnsignedWordTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitUnsignedWordTypeSpecifier(UnsignedWordTypeSpecifier unsignedWordTypeSpecifier)
        {
            Argument.NotNull(unsignedWordTypeSpecifier, () => unsignedWordTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SignedWordTypeSpecifier" />.
        /// </summary>
        /// <param name="signedWordTypeSpecifier">The <see cref="SignedWordTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitSignedWordTypeSpecifier(SignedWordTypeSpecifier signedWordTypeSpecifier)
        {
            Argument.NotNull(signedWordTypeSpecifier, () => signedWordTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="RealTypeSpecifier" />.
        /// </summary>
        /// <param name="realTypeSpecifier">The <see cref="RealTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitRealTypeSpecifier(RealTypeSpecifier realTypeSpecifier)
        {
            Argument.NotNull(realTypeSpecifier, () => realTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerTypeSpecifier" />.
        /// </summary>
        /// <param name="integerTypeSpecifier">The <see cref="IntegerTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitIntegerTypeSpecifier(IntegerTypeSpecifier integerTypeSpecifier)
        {
            Argument.NotNull(integerTypeSpecifier, () => integerTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="EnumerationTypeSpecifier" />.
        /// </summary>
        /// <param name="enumerationTypeSpecifier">The <see cref="EnumerationTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitEnumerationTypeSpecifier(EnumerationTypeSpecifier enumerationTypeSpecifier)
        {
            Argument.NotNull(enumerationTypeSpecifier, () => enumerationTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerRangeTypeSpecifier" />.
        /// </summary>
        /// <param name="integerRangeTypeSpecifier">The <see cref="IntegerRangeTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitIntegerRangeTypeSpecifier(IntegerRangeTypeSpecifier integerRangeTypeSpecifier)
        {
            Argument.NotNull(integerRangeTypeSpecifier, () => integerRangeTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="ArrayTypeSpecifier" />.
        /// </summary>
        /// <param name="arrayTypeSpecifier">The <see cref="ArrayTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitArrayTypeSpecifier(ArrayTypeSpecifier arrayTypeSpecifier)
        {
            Argument.NotNull(arrayTypeSpecifier, () => arrayTypeSpecifier);
            throw new NotImplementedException();
        }






        /// <summary>
        ///     Visits an element of type <see cref="BooleanConstant" />.
        /// </summary>
        /// <param name="booleanConstant">The <see cref="BooleanConstant" /> instance that should be visited.</param>
        public override void VisitBooleanConstant(BooleanConstant booleanConstant)
        {
            Argument.NotNull(booleanConstant, () => booleanConstant);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SymbolicConstant" />.
        /// </summary>
        /// <param name="symbolicConstant">The <see cref="SymbolicConstant" /> instance that should be visited.</param>
        public override void VisitSymbolicConstant(SymbolicConstant symbolicConstant)
        {
            Argument.NotNull(symbolicConstant, () => symbolicConstant);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerConstant" />.
        /// </summary>
        /// <param name="integerConstant">The <see cref="IntegerConstant" /> instance that should be visited.</param>
        public override void VisitIntegerConstant(IntegerConstant integerConstant)
        {
            Argument.NotNull(integerConstant, () => integerConstant);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="RealConstant" />.
        /// </summary>
        /// <param name="realConstant">The <see cref="RealConstant" /> instance that should be visited.</param>
        public override void VisitRealConstant(RealConstant realConstant)
        {
            Argument.NotNull(realConstant, () => realConstant);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="WordConstant" />.
        /// </summary>
        /// <param name="wordConstant">The <see cref="WordConstant" /> instance that should be visited.</param>
        public override void VisitWordConstant(WordConstant wordConstant)
        {
            Argument.NotNull(wordConstant, () => wordConstant);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="RangeConstant" />.
        /// </summary>
        /// <param name="rangeConstant">The <see cref="RangeConstant" /> instance that should be visited.</param>
        public override void VisitRangeConstant(RangeConstant rangeConstant)
        {
            Argument.NotNull(rangeConstant, () => rangeConstant);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="ComplexIdentifierExpression" />.
        /// </summary>
        /// <param name="complexIdentifierExpression">The <see cref="ComplexIdentifierExpression" /> instance that should be visited.</param>
        public override void VisitComplexIdentifierExpression(ComplexIdentifierExpression complexIdentifierExpression)
        {
            Argument.NotNull(complexIdentifierExpression, () => complexIdentifierExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
        public override void VisitUnaryExpression(UnaryExpression unaryExpression)
        {
            Argument.NotNull(unaryExpression, () => unaryExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
        public override void VisitBinaryExpression(BinaryExpression binaryExpression)
        {
            Argument.NotNull(binaryExpression, () => binaryExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="TenaryExpression" />.
        /// </summary>
        /// <param name="tenaryExpression">The <see cref="TenaryExpression" /> instance that should be visited.</param>
        public override void VisitTenaryExpression(TenaryExpression tenaryExpression)
        {
            Argument.NotNull(tenaryExpression, () => tenaryExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IndexSubscriptExpression" />.
        /// </summary>
        /// <param name="indexSubscriptExpression">The <see cref="IndexSubscriptExpression" /> instance that should be visited.</param>
        public override void VisitIndexSubscriptExpression(IndexSubscriptExpression indexSubscriptExpression)
        {
            Argument.NotNull(indexSubscriptExpression, () => indexSubscriptExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SetExpression" />.
        /// </summary>
        /// <param name="setExpression">The <see cref="SetExpression" /> instance that should be visited.</param>
        public override void VisitSetExpression(SetExpression setExpression)
        {
            Argument.NotNull(setExpression, () => setExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="CaseConditionAndEffect" />.
        /// </summary>
        /// <param name="caseConditionAndEffect">The <see cref="CaseConditionAndEffect" /> instance that should be visited.</param>
        public override void VisitCaseConditionAndEffect(CaseConditionAndEffect caseConditionAndEffect)
        {
            Argument.NotNull(caseConditionAndEffect, () => caseConditionAndEffect);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="CaseExpression" />.
        /// </summary>
        /// <param name="caseExpression">The <see cref="CaseExpression" /> instance that should be visited.</param>
        public override void VisitCaseExpression(CaseExpression caseExpression)
        {
            Argument.NotNull(caseExpression, () => caseExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="BasicNextExpression" />.
        /// </summary>
        /// <param name="basicNextExpression">The <see cref="BasicNextExpression" /> instance that should be visited.</param>
        public override void VisitBasicNextExpression(BasicNextExpression basicNextExpression)
        {
            Argument.NotNull(basicNextExpression, () => basicNextExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SimpleExpression" />.
        /// </summary>
        /// <param name="simpleExpression">The <see cref="SimpleExpression" /> instance that should be visited.</param>
        public override void VisitSimpleExpression(SimpleExpression simpleExpression)
        {
            Argument.NotNull(simpleExpression, () => simpleExpression);
            throw new NotImplementedException();
        }










        /// <summary>
        ///     Visits an element of type <see cref="TypedIdentifier" />.
        /// </summary>
        /// <param name="typedIdentifier">The <see cref="TypedIdentifier" /> instance that should be visited.</param>
        public override void VisitTypedIdentifier(TypedIdentifier typedIdentifier)
        {
            Argument.NotNull(typedIdentifier, () => typedIdentifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="SimpleTypedIdentifier" />.
        /// </summary>
        /// <param name="simpleTypedIdentifier">The <see cref="SimpleTypedIdentifier" /> instance that should be visited.</param>
        public override void VisitSimpleTypedIdentifier(SimpleTypedIdentifier simpleTypedIdentifier)
        {
            Argument.NotNull(simpleTypedIdentifier, () => simpleTypedIdentifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="VarDeclaration" />.
        /// </summary>
        /// <param name="varDeclaration">The <see cref="VarDeclaration" /> instance that should be visited.</param>
        public override void VisitVarDeclaration(VarDeclaration varDeclaration)
        {
            Argument.NotNull(varDeclaration, () => varDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IvarDeclaration" />.
        /// </summary>
        /// <param name="ivarDeclaration">The <see cref="IvarDeclaration" /> instance that should be visited.</param>
        public override void VisitIvarDeclaration(IvarDeclaration ivarDeclaration)
        {
            Argument.NotNull(ivarDeclaration, () => ivarDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="FrozenVarDeclaration" />.
        /// </summary>
        /// <param name="frozenVarDeclaration">The <see cref="FrozenVarDeclaration" /> instance that should be visited.</param>
        public override void VisitFrozenVarDeclaration(FrozenVarDeclaration frozenVarDeclaration)
        {
            Argument.NotNull(frozenVarDeclaration, () => frozenVarDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IdentifierExpressionTuple" />.
        /// </summary>
        /// <param name="identifierExpressionTuple">The <see cref="IdentifierExpressionTuple" /> instance that should be visited.</param>
        public override void VisitIdentifierExpressionTuple(IdentifierExpressionTuple identifierExpressionTuple)
        {
            Argument.NotNull(identifierExpressionTuple, () => identifierExpressionTuple);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="DefineDeclaration" />.
        /// </summary>
        /// <param name="defineDeclaration">The <see cref="DefineDeclaration" /> instance that should be visited.</param>
        public override void VisitDefineDeclaration(DefineDeclaration defineDeclaration)
        {
            Argument.NotNull(defineDeclaration, () => defineDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="ConstantsDeclaration" />.
        /// </summary>
        /// <param name="constantsDeclaration">The <see cref="ConstantsDeclaration" /> instance that should be visited.</param>
        public override void VisitConstantsDeclaration(ConstantsDeclaration constantsDeclaration)
        {
            Argument.NotNull(constantsDeclaration, () => constantsDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="InitConstraint" />.
        /// </summary>
        /// <param name="initConstraint">The <see cref="InitConstraint" /> instance that should be visited.</param>
        public override void VisitInitConstraint(InitConstraint initConstraint)
        {
            Argument.NotNull(initConstraint, () => initConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="InvarConstraint" />.
        /// </summary>
        /// <param name="invarConstraint">The <see cref="InvarConstraint" /> instance that should be visited.</param>
        public override void VisitInvarConstraint(InvarConstraint invarConstraint)
        {
            Argument.NotNull(invarConstraint, () => invarConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="TransConstraint" />.
        /// </summary>
        /// <param name="transConstraint">The <see cref="TransConstraint" /> instance that should be visited.</param>
        public override void VisitTransConstraint(TransConstraint transConstraint)
        {
            Argument.NotNull(transConstraint, () => transConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="CurrentStateAssignConstraint" />.
        /// </summary>
        /// <param name="currentStateAssignConstraint">The <see cref="CurrentStateAssignConstraint" /> instance that should be visited.</param>
        public override void VisitCurrentStateAssignConstraint(CurrentStateAssignConstraint currentStateAssignConstraint)
        {
            Argument.NotNull(currentStateAssignConstraint, () => currentStateAssignConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="InitialStateAssignConstraint" />.
        /// </summary>
        /// <param name="initialStateAssignConstraint">The <see cref="InitialStateAssignConstraint" /> instance that should be visited.</param>
        public override void VisitInitialStateAssignConstraint(InitialStateAssignConstraint initialStateAssignConstraint)
        {
            Argument.NotNull(initialStateAssignConstraint, () => initialStateAssignConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="NextStateAssignConstraint" />.
        /// </summary>
        /// <param name="nextStateAssignConstraint">The <see cref="NextStateAssignConstraint" /> instance that should be visited.</param>
        public override void VisitNextStateAssignConstraint(NextStateAssignConstraint nextStateAssignConstraint)
        {
            Argument.NotNull(nextStateAssignConstraint, () => nextStateAssignConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="AssignConstraint" />.
        /// </summary>
        /// <param name="assignConstraint">The <see cref="AssignConstraint" /> instance that should be visited.</param>
        public override void VisitAssignConstraint(AssignConstraint assignConstraint)
        {
            Argument.NotNull(assignConstraint, () => assignConstraint);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="ModuleDeclaration" />.
        /// </summary>
        /// <param name="moduleDeclaration">The <see cref="ModuleDeclaration" /> instance that should be visited.</param>
        public override void VisitModuleDeclaration(ModuleDeclaration moduleDeclaration)
        {
            Argument.NotNull(moduleDeclaration, () => moduleDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="NuXmvModuleTypeSpecifier" />.
        /// </summary>
        /// <param name="nuXmvModuleTypeSpecifier">The <see cref="NuXmvModuleTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitNuXmvModuleTypeSpecifier(NuXmvModuleTypeSpecifier nuXmvModuleTypeSpecifier)
        {
            Argument.NotNull(nuXmvModuleTypeSpecifier, () => nuXmvModuleTypeSpecifier);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="NuXmvProgram" />.
        /// </summary>
        /// <param name="nuXmvProgram">The <see cref="NuXmvProgram" /> instance that should be visited.</param>
        public override void VisitNuXmvProgram(NuXmvProgram nuXmvProgram)
        {
            Argument.NotNull(nuXmvProgram, () => nuXmvProgram);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="PredDeclaration" />.
        /// </summary>
        /// <param name="predDeclaration">The <see cref="PredDeclaration" /> instance that should be visited.</param>
        public override void VisitPredDeclaration(PredDeclaration predDeclaration)
        {
            Argument.NotNull(predDeclaration, () => predDeclaration);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="MirrorDeclaration" />.
        /// </summary>
        /// <param name="mirrorDeclaration">The <see cref="MirrorDeclaration" /> instance that should be visited.</param>
        public override void VisitMirrorDeclaration(MirrorDeclaration mirrorDeclaration)
        {
            Argument.NotNull(mirrorDeclaration, () => mirrorDeclaration);
            throw new NotImplementedException();
        }







        /// <summary>
        ///     Visits an element of type <see cref="CtlSpecification" />.
        /// </summary>
        /// <param name="ctlSpecification">The <see cref="CtlSpecification" /> instance that should be visited.</param>
        public override void VisitCtlSpecification(CtlSpecification ctlSpecification)
        {
            Argument.NotNull(ctlSpecification, () => ctlSpecification);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="CtlSimpleExpression" />.
        /// </summary>
        /// <param name="ctlSimpleExpression">The <see cref="CtlSimpleExpression" /> instance that should be visited.</param>
        public override void VisitCtlSimpleExpression(CtlSimpleExpression ctlSimpleExpression)
        {
            Argument.NotNull(ctlSimpleExpression, () => ctlSimpleExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="CtlBinaryExpression" />.
        /// </summary>
        /// <param name="ctlBinaryExpression">The <see cref="CtlBinaryExpression" /> instance that should be visited.</param>
        public override void VisitCtlBinaryExpression(CtlBinaryExpression ctlBinaryExpression)
        {
            Argument.NotNull(ctlBinaryExpression, () => ctlBinaryExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="CtlUnaryExpression" />.
        /// </summary>
        /// <param name="ctlUnaryExpression">The <see cref="CtlUnaryExpression" /> instance that should be visited.</param>
        public override void VisitCtlUnaryExpression(CtlUnaryExpression ctlUnaryExpression)
        {
            Argument.NotNull(ctlUnaryExpression, () => ctlUnaryExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlSpecification" />.
        /// </summary>
        /// <param name="ltlSpecification">The <see cref="LtlSpecification" /> instance that should be visited.</param>
        public override void VisitLtlSpecification(LtlSpecification ltlSpecification)
        {
            Argument.NotNull(ltlSpecification, () => ltlSpecification);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlSimpleExpression" />.
        /// </summary>
        /// <param name="ltlSimpleExpression">The <see cref="LtlSimpleExpression" /> instance that should be visited.</param>
        public override void VisitLtlSimpleExpression(LtlSimpleExpression ltlSimpleExpression)
        {
            Argument.NotNull(ltlSimpleExpression, () => ltlSimpleExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlBinaryExpression" />.
        /// </summary>
        /// <param name="ltlBinaryExpression">The <see cref="LtlBinaryExpression" /> instance that should be visited.</param>
        public override void VisitLtlBinaryExpression(LtlBinaryExpression ltlBinaryExpression)
        {
            Argument.NotNull(ltlBinaryExpression, () => ltlBinaryExpression);
            throw new NotImplementedException();
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlUnaryExpression" />.
        /// </summary>
        /// <param name="ltlUnaryExpression">The <see cref="LtlUnaryExpression" /> instance that should be visited.</param>
        public override void VisitLtlUnaryExpression(LtlUnaryExpression ltlUnaryExpression)
        {
            Argument.NotNull(ltlUnaryExpression, () => ltlUnaryExpression);
            throw new NotImplementedException();
        }

    }
}