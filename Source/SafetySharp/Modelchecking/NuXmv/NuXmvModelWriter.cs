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
    using System.Text;
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


        #region Identifier
        /// <summary>
        ///     Visits an element of type <see cref="Identifier" />.
        /// </summary>
        /// <param name="identifier">The <see cref="Identifier" /> instance that should be visited.</param>
        public override void VisitIdentifier(Identifier identifier)
        {
            Argument.NotNull(identifier, () => identifier);
            CodeWriter.Append(identifier.Name);
        }

        /// <summary>
        ///     Visits an element of type <see cref="NameComplexIdentifier" />.
        /// </summary>
        /// <param name="nameComplexIdentifier">The <see cref="NameComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitNameComplexIdentifier(NameComplexIdentifier nameComplexIdentifier)
        {
            Argument.NotNull(nameComplexIdentifier, () => nameComplexIdentifier);
            // NestedComplexIdentifier : Identifier
            nameComplexIdentifier.NameIdentifier.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="NestedComplexIdentifier" />.
        /// </summary>
        /// <param name="nestedComplexIdentifier">The <see cref="NestedComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitNestedComplexIdentifier(NestedComplexIdentifier nestedComplexIdentifier)
        {
            Argument.NotNull(nestedComplexIdentifier, () => nestedComplexIdentifier);
            // NestedComplexIdentifier : Container '.' NameIdentifier
            nestedComplexIdentifier.Container.Accept(this);
            CodeWriter.Append(".");
            nestedComplexIdentifier.NameIdentifier.Accept(this);

        }

        /// <summary>
        ///     Visits an element of type <see cref="ArrayAccessComplexIdentifier" />.
        /// </summary>
        /// <param name="arrayAccessComplexIdentifier">The <see cref="ArrayAccessComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitArrayAccessComplexIdentifier(ArrayAccessComplexIdentifier arrayAccessComplexIdentifier)
        {
            Argument.NotNull(arrayAccessComplexIdentifier, () => arrayAccessComplexIdentifier);
            // NestedComplexIdentifier : Container '[' Index ']'
            arrayAccessComplexIdentifier.Container.Accept(this);
            CodeWriter.Append("[");
            arrayAccessComplexIdentifier.Index.Accept(this);
            CodeWriter.Append("]");
        }

        /// <summary>
        ///     Visits an element of type <see cref="SelfComplexIdentifier" />.
        /// </summary>
        /// <param name="selfComplexIdentifier">The <see cref="SelfComplexIdentifier" /> instance that should be visited.</param>
        public override void VisitSelfComplexIdentifier(SelfComplexIdentifier selfComplexIdentifier)
        {
            Argument.NotNull(selfComplexIdentifier, () => selfComplexIdentifier);
            CodeWriter.Append("self");
        }
        #endregion

        #region Type
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
        #endregion

        #region TypeSpecifier

        /// <summary>
        ///     Visits an element of type <see cref="BooleanTypeSpecifier" />.
        /// </summary>
        /// <param name="booleanTypeSpecifier">The <see cref="BooleanTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitBooleanTypeSpecifier(BooleanTypeSpecifier booleanTypeSpecifier)
        {
            Argument.NotNull(booleanTypeSpecifier, () => booleanTypeSpecifier);
            CodeWriter.Append("boolean");
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnsignedWordTypeSpecifier" />.
        /// </summary>
        /// <param name="unsignedWordTypeSpecifier">The <see cref="UnsignedWordTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitUnsignedWordTypeSpecifier(UnsignedWordTypeSpecifier unsignedWordTypeSpecifier)
        {
            Argument.NotNull(unsignedWordTypeSpecifier, () => unsignedWordTypeSpecifier);
            CodeWriter.Append("unsigned word [");
            unsignedWordTypeSpecifier.Length.Accept(this);
            CodeWriter.Append("]");
        }

        /// <summary>
        ///     Visits an element of type <see cref="SignedWordTypeSpecifier" />.
        /// </summary>
        /// <param name="signedWordTypeSpecifier">The <see cref="SignedWordTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitSignedWordTypeSpecifier(SignedWordTypeSpecifier signedWordTypeSpecifier)
        {
            Argument.NotNull(signedWordTypeSpecifier, () => signedWordTypeSpecifier);
            CodeWriter.Append("signed word [");
            signedWordTypeSpecifier.Length.Accept(this);
            CodeWriter.Append("]");
        }

        /// <summary>
        ///     Visits an element of type <see cref="RealTypeSpecifier" />.
        /// </summary>
        /// <param name="realTypeSpecifier">The <see cref="RealTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitRealTypeSpecifier(RealTypeSpecifier realTypeSpecifier)
        {
            Argument.NotNull(realTypeSpecifier, () => realTypeSpecifier);
            CodeWriter.Append("real");
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerTypeSpecifier" />.
        /// </summary>
        /// <param name="integerTypeSpecifier">The <see cref="IntegerTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitIntegerTypeSpecifier(IntegerTypeSpecifier integerTypeSpecifier)
        {
            Argument.NotNull(integerTypeSpecifier, () => integerTypeSpecifier);
            CodeWriter.Append("integer");
        }

        /// <summary>
        ///     Visits an element of type <see cref="EnumerationTypeSpecifier" />.
        /// </summary>
        /// <param name="enumerationTypeSpecifier">The <see cref="EnumerationTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitEnumerationTypeSpecifier(EnumerationTypeSpecifier enumerationTypeSpecifier)
        {
            Argument.NotNull(enumerationTypeSpecifier, () => enumerationTypeSpecifier);
            CodeWriter.Append("{{ ");
            var first = true;
            foreach (var constExpression in enumerationTypeSpecifier.Domain)
            {
                //constExpression is a Literal which may be a symbolic_constant or an integer
                //TODO: Put this check into a validation
                if (!(constExpression is SymbolicConstant || constExpression is IntegerConstant))
                    throw new Exception("enumerationType can only be an integer or a symbolic constant (no real,boolean...) ");
                if (!first)
                    CodeWriter.AppendLine(", ");
                first = false;
                constExpression.Accept(this);
            }
            CodeWriter.Append(" }}");
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerRangeTypeSpecifier" />.
        /// </summary>
        /// <param name="integerRangeTypeSpecifier">The <see cref="IntegerRangeTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitIntegerRangeTypeSpecifier(IntegerRangeTypeSpecifier integerRangeTypeSpecifier)
        {
            Argument.NotNull(integerRangeTypeSpecifier, () => integerRangeTypeSpecifier);
            integerRangeTypeSpecifier.Lower.Accept(this);
            CodeWriter.Append(" .. ");
            integerRangeTypeSpecifier.Upper.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="ArrayTypeSpecifier" />.
        /// </summary>
        /// <param name="arrayTypeSpecifier">The <see cref="ArrayTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitArrayTypeSpecifier(ArrayTypeSpecifier arrayTypeSpecifier)
        {
            Argument.NotNull(arrayTypeSpecifier, () => arrayTypeSpecifier);
            CodeWriter.Append("array ");
            arrayTypeSpecifier.Lower.Accept(this);
            CodeWriter.Append(" .. ");
            arrayTypeSpecifier.Upper.Accept(this);
            CodeWriter.Append(" of ");
            arrayTypeSpecifier.ElementTypeSpecifier.Accept(this);

        }
        #endregion

        #region Expressions

        #region Constant Expressions
        /// <summary>
        ///     Visits an element of type <see cref="BooleanConstant" />.
        /// </summary>
        /// <param name="booleanConstant">The <see cref="BooleanConstant" /> instance that should be visited.</param>
        public override void VisitBooleanConstant(BooleanConstant booleanConstant)
        {
            Argument.NotNull(booleanConstant, () => booleanConstant);
            if (booleanConstant.Value)
                CodeWriter.Append("TRUE");
            else
                CodeWriter.Append("FALSE");
        }

        /// <summary>
        ///     Visits an element of type <see cref="SymbolicConstant" />.
        /// </summary>
        /// <param name="symbolicConstant">The <see cref="SymbolicConstant" /> instance that should be visited.</param>
        public override void VisitSymbolicConstant(SymbolicConstant symbolicConstant)
        {
            Argument.NotNull(symbolicConstant, () => symbolicConstant);
            symbolicConstant.Identifier.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="IntegerConstant" />.
        /// </summary>
        /// <param name="integerConstant">The <see cref="IntegerConstant" /> instance that should be visited.</param>
        public override void VisitIntegerConstant(IntegerConstant integerConstant)
        {
            Argument.NotNull(integerConstant, () => integerConstant);
            CodeWriter.Append(integerConstant.Value.ToString());
        }

        /// <summary>
        ///     Visits an element of type <see cref="RealConstant" />.
        /// </summary>
        /// <param name="realConstant">The <see cref="RealConstant" /> instance that should be visited.</param>
        public override void VisitRealConstant(RealConstant realConstant)
        {
            Argument.NotNull(realConstant, () => realConstant);
            CodeWriter.Append(realConstant.Value.ToString());
        }

        /// <summary>
        ///     Visits an element of type <see cref="WordConstant" />.
        /// </summary>
        /// <param name="wordConstant">The <see cref="WordConstant" /> instance that should be visited.</param>
        //TODO:  Extract to own function. And: Write Tests, many Tests!
        //TODO:  Add ImproveReadability to every case
        public override void VisitWordConstant(WordConstant wordConstant)
        {
            Argument.NotNull(wordConstant, () => wordConstant);
            string sign;
            string radix;
            var number=new StringBuilder();
            switch (wordConstant.SignSpecifier)
            {
                case NuXmvSignSpecifier.SignedSpecifier:
                    sign = "s";
                    break;
                case NuXmvSignSpecifier.UnsignedSpecifier:
                    sign = "u";
                    break;
                default:
                    sign = "u";
                    break;
            }
            switch (wordConstant.Base)
            {
                case NuXmvRadix.BinaryRadix:
                    radix = "b";
                    for (int i=0; i<wordConstant.Value.Length; i++)
                    {
                        if (wordConstant.Value[i])
                            number.Append("1");
                        if (!wordConstant.Value[i])
                            number.Append("0");
                    }
                    break;
                case NuXmvRadix.OctalRadix:
                    radix = "o";
                    if ((wordConstant.Value.Length % 3) != 0)
                        throw new Exception("Not convertable, because radix not mod 3");
                    for (int i = 0; i < (wordConstant.Value.Length / 3); i++)
                    {
                        int n4 = wordConstant.Value[i]     ? 4 : 0;
                        int n2 = wordConstant.Value[i + 1] ? 2 : 0;
                        int n1 = wordConstant.Value[i + 2] ? 1 : 0;
                        number.Append((n4 + n2 + n1).ToString("X"));
                    }
                    break;
                case NuXmvRadix.DecimalRadix:
                    radix = "d";
                    if (wordConstant.SignSpecifier == NuXmvSignSpecifier.UnsignedSpecifier)
                    {
                        int acc = 0;
                        int pot = 1;

                        for (int i = wordConstant.Value.Length - 1; i >= 0; i--, pot *= 2)
                        {
                            if (wordConstant.Value[i])
                                acc += pot;
                        }
                        number.Append(acc.ToString());
                    }
                    if (wordConstant.SignSpecifier == NuXmvSignSpecifier.SignedSpecifier)
                    {
                        var isPositive = wordConstant.Value[0];
                        int acc = 0;
                        int pot = 1;
                        //negative 2-complement: negate every bit and add 1 afterwards
                        for (int i = wordConstant.Value.Length - 1; i >= 1; i--, pot *= 2)
                        {
                            if (wordConstant.Value[i] && isPositive)
                                acc += pot;
                            if (!wordConstant.Value[i] && !isPositive) //negate every bit
                                acc += pot;
                        }
                        if (!isPositive)
                        {
                            acc++; //add 1
                            number.Append("-"); //Alternative: negate by acc *= -1; 
                        }
                        number.Append(acc.ToString());

                    }
                    break;
                case NuXmvRadix.HexadecimalRadix:
                    radix = "h";
                    if ((wordConstant.Value.Length % 4) != 0)
                        throw new Exception("Not convertable, because radix not mod 4");
                    for (int i = 0; i < (wordConstant.Value.Length / 4); i++)
                    {
                        int n8 = wordConstant.Value[i    ] ? 8 : 0;
                        int n4 = wordConstant.Value[i + 1] ? 4 : 0;
                        int n2 = wordConstant.Value[i + 2] ? 2 : 0;
                        int n1 = wordConstant.Value[i + 3] ? 1 : 0;
                        number.Append((n8 + n4 + n2 + n1).ToString("X"));
                    }
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
            //if (wordConstant.ImproveReadability && (i+1)%3==0 && i + 1 < wordConstant.Value.Length)
            //          number.Append("_");

            CodeWriter.Append("0{0}{1}{2}_{3}",sign,radix, wordConstant.Value.Length,number);
        }

        /// <summary>
        ///     Visits an element of type <see cref="RangeConstant" />.
        /// </summary>
        /// <param name="rangeConstant">The <see cref="RangeConstant" /> instance that should be visited.</param>
        public override void VisitRangeConstant(RangeConstant rangeConstant)
        {
            Argument.NotNull(rangeConstant, () => rangeConstant);
            CodeWriter.Append("{0}..{1}", rangeConstant.From.ToString(), rangeConstant.To.ToString());
        }
        #endregion

        #region Basic Expression

        /// <summary>
        ///     Visits an element of type <see cref="ComplexIdentifierExpression" />.
        /// </summary>
        /// <param name="complexIdentifierExpression">The <see cref="ComplexIdentifierExpression" /> instance that should be visited.</param>
        public override void VisitComplexIdentifierExpression(ComplexIdentifierExpression complexIdentifierExpression)
        {
            Argument.NotNull(complexIdentifierExpression, () => complexIdentifierExpression);
            complexIdentifierExpression.Identifier.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
        public override void VisitUnaryExpression(UnaryExpression unaryExpression)
        {
            Argument.NotNull(unaryExpression, () => unaryExpression);
            switch (unaryExpression.Operator)
            {
                case NuXmvUnaryOperator.LogicalNot:
                    CodeWriter.Append("! (");
                    unaryExpression.Expression.Accept(this);
                    CodeWriter.Append(")");
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
        }

        /// <summary>
        ///     Visits an element of type <see cref="BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
        public override void VisitBinaryExpression(BinaryExpression binaryExpression)
        {
            Argument.NotNull(binaryExpression, () => binaryExpression);
            CodeWriter.Append("(");
            switch (binaryExpression.Operator)
            {
                case NuXmvBinaryOperator.LogicalAnd:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("&");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LogicalOr:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("|");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LogicalXor:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("xor");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LogicalNxor:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("nxor");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LogicalImplies:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("->");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LogicalEquivalence:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("<->");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.Equality:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("=");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.Inequality:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("!=");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LessThan:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("<");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.GreaterThan:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append(">");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.LessEqual:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("<=");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.GreaterEqual:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append(">=");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.IntegerAddition:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("+");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.IntegerSubtraction:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("-");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.IntegerMultiplication:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("*");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.IntegerDivision:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("/");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.IntegerRemainder:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("mod");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.BitShiftRight:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append(">>");
                    binaryExpression.Right.Accept(this);
                    break;
                case NuXmvBinaryOperator.BitShiftLeft:
                    binaryExpression.Left.Accept(this);
                    CodeWriter.Append("<<");
                    binaryExpression.Right.Accept(this);
                    break;
                //TODO: Other BinaryExpressions like word1, bool, which have a prefix-operator
                default:
                    throw new ArgumentOutOfRangeException();
            }
            CodeWriter.Append(")");
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
            indexSubscriptExpression.ExpressionLeadingToArray.Accept(this);
            CodeWriter.Append("[");
            indexSubscriptExpression.Index.Accept(this);
            CodeWriter.Append("]");
        }

        /// <summary>
        ///     Visits an element of type <see cref="SetExpression" />.
        /// </summary>
        /// <param name="setExpression">The <see cref="SetExpression" /> instance that should be visited.</param>
        public override void VisitSetExpression(SetExpression setExpression)
        {
            Argument.NotNull(setExpression, () => setExpression);

            CodeWriter.Append("{{ ");
            var first = true;
            foreach (var expression in setExpression.SetBodyExpression)
            {
                if (!first)
                    CodeWriter.AppendLine(", ");
                first = false;
                expression.Accept(this);
            }
            CodeWriter.Append(" }}");
        }

        /// <summary>
        ///     Visits an element of type <see cref="CaseConditionAndEffect" />.
        /// </summary>
        /// <param name="caseConditionAndEffect">The <see cref="CaseConditionAndEffect" /> instance that should be visited.</param>
        public override void VisitCaseConditionAndEffect(CaseConditionAndEffect caseConditionAndEffect)
        {
            Argument.NotNull(caseConditionAndEffect, () => caseConditionAndEffect);

            caseConditionAndEffect.CaseCondition.Accept(this);
            CodeWriter.Append(" : ");
            caseConditionAndEffect.CaseEffect.Accept(this);
            CodeWriter.AppendLine(" ;");
        }

        /// <summary>
        ///     Visits an element of type <see cref="CaseExpression" />.
        /// </summary>
        /// <param name="caseExpression">The <see cref="CaseExpression" /> instance that should be visited.</param>
        public override void VisitCaseExpression(CaseExpression caseExpression)
        {
            Argument.NotNull(caseExpression, () => caseExpression);
            CodeWriter.AppendLine("case");
            CodeWriter.IncreaseIndent();
            foreach (var caseConditionAndEffect in caseExpression.CaseBody)
            {
                caseConditionAndEffect.Accept(this);
            }
            CodeWriter.DecreaseIndent();;
            CodeWriter.AppendLine("esac");
        }

        /// <summary>
        ///     Visits an element of type <see cref="BasicNextExpression" />.
        /// </summary>
        /// <param name="basicNextExpression">The <see cref="BasicNextExpression" /> instance that should be visited.</param>
        public override void VisitBasicNextExpression(BasicNextExpression basicNextExpression)
        {
            Argument.NotNull(basicNextExpression, () => basicNextExpression);
            CodeWriter.Append("next(");
            basicNextExpression.Expression.Accept(this);
            CodeWriter.Append(")");
        }

        /// <summary>
        ///     Visits an element of type <see cref="SimpleExpression" />.
        /// </summary>
        /// <param name="simpleExpression">The <see cref="SimpleExpression" /> instance that should be visited.</param>
        public override void VisitSimpleExpression(SimpleExpression simpleExpression)
        {
            Argument.NotNull(simpleExpression, () => simpleExpression);

            //TODO: Validation: Check if no next() is included
            simpleExpression.NestedExpression.Accept(this);
        }
        #endregion

        #endregion
        
        #region Finite State Machine

        // Chapter 2.3.1 Variable Declarations p 23-26.

        /// <summary>
        ///     Visits an element of type <see cref="TypedIdentifier" />.
        /// </summary>
        /// <param name="typedIdentifier">The <see cref="TypedIdentifier" /> instance that should be visited.</param>
        public override void VisitTypedIdentifier(TypedIdentifier typedIdentifier)
        {
            Argument.NotNull(typedIdentifier, () => typedIdentifier);
            typedIdentifier.Identifier.Accept(this);
            CodeWriter.Append(" : ");
            typedIdentifier.TypeSpecifier.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="SimpleTypedIdentifier" />.
        /// </summary>
        /// <param name="simpleTypedIdentifier">The <see cref="SimpleTypedIdentifier" /> instance that should be visited.</param>
        public override void VisitSimpleTypedIdentifier(SimpleTypedIdentifier simpleTypedIdentifier)
        {
            Argument.NotNull(simpleTypedIdentifier, () => simpleTypedIdentifier);
            simpleTypedIdentifier.Identifier.Accept(this);
            CodeWriter.Append(" : ");
            simpleTypedIdentifier.TypeSpecifier.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="VarDeclaration" />.
        /// </summary>
        /// <param name="varDeclaration">The <see cref="VarDeclaration" /> instance that should be visited.</param>
        public override void VisitVarDeclaration(VarDeclaration varDeclaration)
        {
            Argument.NotNull(varDeclaration, () => varDeclaration);
            CodeWriter.AppendLine("VAR");
            CodeWriter.IncreaseIndent();
            foreach (var typedIdentifier in varDeclaration.Variables)
            {
                typedIdentifier.Accept(this);
                CodeWriter.AppendLine(";");
            }
            CodeWriter.DecreaseIndent();
        }

        /// <summary>
        ///     Visits an element of type <see cref="IvarDeclaration" />.
        /// </summary>
        /// <param name="ivarDeclaration">The <see cref="IvarDeclaration" /> instance that should be visited.</param>
        public override void VisitIvarDeclaration(IvarDeclaration ivarDeclaration)
        {
            Argument.NotNull(ivarDeclaration, () => ivarDeclaration);
            CodeWriter.AppendLine("IVAR");
            CodeWriter.IncreaseIndent();
            foreach (var typedIdentifier in ivarDeclaration.InputVariables)
            {
                typedIdentifier.Accept(this);
                CodeWriter.AppendLine(";");
            }
            CodeWriter.DecreaseIndent();
        }

        /// <summary>
        ///     Visits an element of type <see cref="FrozenVarDeclaration" />.
        /// </summary>
        /// <param name="frozenVarDeclaration">The <see cref="FrozenVarDeclaration" /> instance that should be visited.</param>
        public override void VisitFrozenVarDeclaration(FrozenVarDeclaration frozenVarDeclaration)
        {
            Argument.NotNull(frozenVarDeclaration, () => frozenVarDeclaration);
            CodeWriter.AppendLine("FROZENVAR");
            CodeWriter.IncreaseIndent();
            foreach (var typedIdentifier in frozenVarDeclaration.FrozenVariables)
            {
                typedIdentifier.Accept(this);
                CodeWriter.AppendLine(";");
            }
            CodeWriter.DecreaseIndent();
        }


        // Chapter 2.3.2 DEFINE Declarations p 26

        /// <summary>
        ///     Visits an element of type <see cref="IdentifierExpressionTuple" />.
        /// </summary>
        /// <param name="identifierExpressionTuple">The <see cref="IdentifierExpressionTuple" /> instance that should be visited.</param>
        public override void VisitIdentifierExpressionTuple(IdentifierExpressionTuple identifierExpressionTuple)
        {
            Argument.NotNull(identifierExpressionTuple, () => identifierExpressionTuple);
            identifierExpressionTuple.Identifier.Accept(this);
            CodeWriter.Append(" := ");
            identifierExpressionTuple.Expression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="DefineDeclaration" />.
        /// </summary>
        /// <param name="defineDeclaration">The <see cref="DefineDeclaration" /> instance that should be visited.</param>
        public override void VisitDefineDeclaration(DefineDeclaration defineDeclaration)
        {
            Argument.NotNull(defineDeclaration, () => defineDeclaration);
            CodeWriter.AppendLine("DEFINE");
            CodeWriter.IncreaseIndent();
            foreach (var identifierExpressionTuple in defineDeclaration.Defines)
            {
                identifierExpressionTuple.Accept(this);
                CodeWriter.AppendLine(";");
            }
            CodeWriter.DecreaseIndent();
        }

        // Chapter 2.3.4 CONSTANTS Declarations p 27

        /// <summary>
        ///     Visits an element of type <see cref="ConstantsDeclaration" />.
        /// </summary>
        /// <param name="constantsDeclaration">The <see cref="ConstantsDeclaration" /> instance that should be visited.</param>
        public override void VisitConstantsDeclaration(ConstantsDeclaration constantsDeclaration)
        {
            Argument.NotNull(constantsDeclaration, () => constantsDeclaration);
            CodeWriter.AppendLine("CONSTANTS");
            CodeWriter.IncreaseIndent();
            var first = true;
            foreach (var identifier in constantsDeclaration.Constants)
            {
                if (!first)
                    CodeWriter.AppendLine(", ");
                first = false;
                identifier.Accept(this);
            }
            CodeWriter.DecreaseIndent();
        }

        // Chapter 2.3.5 INIT Constraint p 27

        /// <summary>
        ///     Visits an element of type <see cref="InitConstraint" />.
        /// </summary>
        /// <param name="initConstraint">The <see cref="InitConstraint" /> instance that should be visited.</param>
        public override void VisitInitConstraint(InitConstraint initConstraint)
        {
            Argument.NotNull(initConstraint, () => initConstraint);
            CodeWriter.AppendLine("INIT");
            CodeWriter.IncreaseIndent();
            initConstraint.Expression.Accept(this);
            CodeWriter.DecreaseIndent();
        }

        // Chapter 2.3.6 INVAR Constraint p 27

        /// <summary>
        ///     Visits an element of type <see cref="InvarConstraint" />.
        /// </summary>
        /// <param name="invarConstraint">The <see cref="InvarConstraint" /> instance that should be visited.</param>
        public override void VisitInvarConstraint(InvarConstraint invarConstraint)
        {
            Argument.NotNull(invarConstraint, () => invarConstraint);
            CodeWriter.AppendLine("INVAR");
            CodeWriter.IncreaseIndent();
            invarConstraint.Expression.Accept(this);
            CodeWriter.DecreaseIndent();
        }

        // Chapter 2.3.7 TRANS Constraint p 28

        /// <summary>
        ///     Visits an element of type <see cref="TransConstraint" />.
        /// </summary>
        /// <param name="transConstraint">The <see cref="TransConstraint" /> instance that should be visited.</param>
        public override void VisitTransConstraint(TransConstraint transConstraint)
        {
            Argument.NotNull(transConstraint, () => transConstraint);
            CodeWriter.AppendLine("TRANS");
            CodeWriter.IncreaseIndent();
            transConstraint.Expression.Accept(this);
            CodeWriter.DecreaseIndent();
        }

        // Chapter 2.3.8 ASSIGN Constraint p 28-29

        /// <summary>
        ///     Visits an element of type <see cref="CurrentStateAssignConstraint" />.
        /// </summary>
        /// <param name="currentStateAssignConstraint">The <see cref="CurrentStateAssignConstraint" /> instance that should be visited.</param>
        public override void VisitCurrentStateAssignConstraint(CurrentStateAssignConstraint currentStateAssignConstraint)
        {
            Argument.NotNull(currentStateAssignConstraint, () => currentStateAssignConstraint);
            currentStateAssignConstraint.Identifier.Accept(this);
            CodeWriter.Append(" := ");
            currentStateAssignConstraint.Expression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="InitialStateAssignConstraint" />.
        /// </summary>
        /// <param name="initialStateAssignConstraint">The <see cref="InitialStateAssignConstraint" /> instance that should be visited.</param>
        public override void VisitInitialStateAssignConstraint(InitialStateAssignConstraint initialStateAssignConstraint)
        {
            Argument.NotNull(initialStateAssignConstraint, () => initialStateAssignConstraint);
            CodeWriter.Append("init (");
            initialStateAssignConstraint.Identifier.Accept(this);
            CodeWriter.Append(") := ");
            initialStateAssignConstraint.Expression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="NextStateAssignConstraint" />.
        /// </summary>
        /// <param name="nextStateAssignConstraint">The <see cref="NextStateAssignConstraint" /> instance that should be visited.</param>
        public override void VisitNextStateAssignConstraint(NextStateAssignConstraint nextStateAssignConstraint)
        {
            Argument.NotNull(nextStateAssignConstraint, () => nextStateAssignConstraint);
            CodeWriter.Append("next (");
            nextStateAssignConstraint.Identifier.Accept(this);
            CodeWriter.Append(") := ");
            nextStateAssignConstraint.Expression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="AssignConstraint" />.
        /// </summary>
        /// <param name="assignConstraint">The <see cref="AssignConstraint" /> instance that should be visited.</param>
        public override void VisitAssignConstraint(AssignConstraint assignConstraint)
        {
            Argument.NotNull(assignConstraint, () => assignConstraint);

            CodeWriter.AppendLine("ASSIGN");
            CodeWriter.IncreaseIndent();
            foreach (var singleAssignConstraint in assignConstraint.Assigns)
            {
                singleAssignConstraint.Accept(this);
                CodeWriter.AppendLine(";");
            }
            CodeWriter.DecreaseIndent();
        }


        // Chapter 2.3.9 FAIRNESS Constraints p 30
        // TODO
        // Chapter 2.3.10 MODULE Declarations p 30-31  

        /// <summary>
        ///     Visits an element of type <see cref="ModuleDeclaration" />.
        /// </summary>
        /// <param name="moduleDeclaration">The <see cref="ModuleDeclaration" /> instance that should be visited.</param>
        public override void VisitModuleDeclaration(ModuleDeclaration moduleDeclaration)
        {
            Argument.NotNull(moduleDeclaration, () => moduleDeclaration);

            CodeWriter.Append("MODULE ");
            moduleDeclaration.Identifier.Accept(this);
            if (moduleDeclaration.ModuleParameters.Length > 0)
            {
                CodeWriter.Append("(");
                var first = true;
                foreach (var moduleParameter in moduleDeclaration.ModuleParameters)
                {
                    if (!first)
                        CodeWriter.AppendLine(", ");
                    first = false;
                    moduleParameter.Accept(this);
                }
                CodeWriter.Append(")");
            }
            CodeWriter.NewLine();
            CodeWriter.IncreaseIndent();

            foreach (var moduleElement in moduleDeclaration.ModuleElements)
            {
                moduleElement.Accept(this);
                CodeWriter.NewLine();
            }
            CodeWriter.DecreaseIndent();
            CodeWriter.NewLine();
        }

        // Chapter 2.3.11 MODULE Instantiations p 31.

        /// <summary>
        ///     Visits an element of type <see cref="NuXmvModuleTypeSpecifier" />.
        /// </summary>
        /// <param name="nuXmvModuleTypeSpecifier">The <see cref="NuXmvModuleTypeSpecifier" /> instance that should be visited.</param>
        public override void VisitNuXmvModuleTypeSpecifier(NuXmvModuleTypeSpecifier nuXmvModuleTypeSpecifier)
        {
            Argument.NotNull(nuXmvModuleTypeSpecifier, () => nuXmvModuleTypeSpecifier);
            nuXmvModuleTypeSpecifier.ModuleName.Accept(this);
            if (nuXmvModuleTypeSpecifier.ModuleParameters.Length > 0)
            {
                CodeWriter.Append("(");
                var first = true;
                foreach (var moduleParameter in nuXmvModuleTypeSpecifier.ModuleParameters)
                {
                    if (!first)
                        CodeWriter.AppendLine(", ");
                    first = false;
                    moduleParameter.Accept(this);
                }
                CodeWriter.Append(")");
            }
            //semicolon and newline written by visitor of VAR-Section
        }

        // Chapter 2.3.12 References to Module Components (Variables and Defines) p 32-33
        // moved to the namespace SafetySharp.Modelchecking.NuXmv, because there is also identifier

        // Chapter 2.3.13 A Program and the main Module p 33

        /// <summary>
        ///     Visits an element of type <see cref="NuXmvProgram" />.
        /// </summary>
        /// <param name="nuXmvProgram">The <see cref="NuXmvProgram" /> instance that should be visited.</param>
        public override void VisitNuXmvProgram(NuXmvProgram nuXmvProgram)
        {
            Argument.NotNull(nuXmvProgram, () => nuXmvProgram);

            foreach (var module in nuXmvProgram.Modules)
            {
                module.Accept(this);
            }
        }


        // Chapter 2.3.14 Namespaces and Constraints on Declarations p 33
        // just description
        // Chapter 2.3.15 Context p 34
        // just description
        // Chapter 2.3.16 ISA Declarations p 34 (depreciated)
        // don't implement as it is depreciated
        // Chapter 2.3.17 PRED and MIRROR Declarations p 34-35
        //TODO: Useful for debugging and CEGAR (Counterexample Guided Abstraction Refinement)

        /// <summary>
        ///     Visits an element of type <see cref="PredDeclaration" />.
        /// </summary>
        /// <param name="predDeclaration">The <see cref="PredDeclaration" /> instance that should be visited.</param>
        public override void VisitPredDeclaration(PredDeclaration predDeclaration)
        {
            Argument.NotNull(predDeclaration, () => predDeclaration);
            CodeWriter.Append("PRED ");
            if (predDeclaration.Identifier != null)
            {
                CodeWriter.Append(" < ");
                predDeclaration.Identifier.Accept(this);
                CodeWriter.Append(" > := ");
            }
            predDeclaration.Expression.Accept(this);
            CodeWriter.NewLine();
        }

        /// <summary>
        ///     Visits an element of type <see cref="MirrorDeclaration" />.
        /// </summary>
        /// <param name="mirrorDeclaration">The <see cref="MirrorDeclaration" /> instance that should be visited.</param>
        public override void VisitMirrorDeclaration(MirrorDeclaration mirrorDeclaration)
        {
            Argument.NotNull(mirrorDeclaration, () => mirrorDeclaration);
            CodeWriter.Append("MIRROR ");
            mirrorDeclaration.VariableIdentifier.Accept(this);
            CodeWriter.NewLine();
        }
        #endregion

        #region Specification

        /// <summary>
        ///     Visits an element of type <see cref="CtlSpecification" />.
        /// </summary>
        /// <param name="ctlSpecification">The <see cref="CtlSpecification" /> instance that should be visited.</param>
        public override void VisitCtlSpecification(CtlSpecification ctlSpecification)
        {
            Argument.NotNull(ctlSpecification, () => ctlSpecification);
            //TODO allow named specifications
            CodeWriter.Append("CTLSPEC ");
            ctlSpecification.CtlExpression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="CtlSimpleExpression" />.
        /// </summary>
        /// <param name="ctlSimpleExpression">The <see cref="CtlSimpleExpression" /> instance that should be visited.</param>
        public override void VisitCtlSimpleExpression(CtlSimpleExpression ctlSimpleExpression)
        {
            Argument.NotNull(ctlSimpleExpression, () => ctlSimpleExpression);
            ctlSimpleExpression.Expression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="CtlBinaryExpression" />.
        /// </summary>
        /// <param name="ctlBinaryExpression">The <see cref="CtlBinaryExpression" /> instance that should be visited.</param>
        public override void VisitCtlBinaryExpression(CtlBinaryExpression ctlBinaryExpression)
        {
            Argument.NotNull(ctlBinaryExpression, () => ctlBinaryExpression);
            CodeWriter.Append("(");
            switch (ctlBinaryExpression.Operator)
            {
                case NuXmvCtlBinaryOperator.LogicalAnd:
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("&");
                    ctlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvCtlBinaryOperator.LogicalOr:
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("|");
                    ctlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvCtlBinaryOperator.LogicalXor:
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("xor");
                    ctlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvCtlBinaryOperator.LogicalNxor:
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("nxor");
                    ctlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvCtlBinaryOperator.LogicalImplies:
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("->");
                    ctlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvCtlBinaryOperator.LogicalEquivalence:
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("<->");
                    ctlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvCtlBinaryOperator.ExistsUntil:
                    CodeWriter.Append("E [");
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append(" U ");
                    ctlBinaryExpression.Right.Accept(this);
                    CodeWriter.Append(" ] ");
                    break;
                case NuXmvCtlBinaryOperator.ForallUntil:
                    CodeWriter.Append("A [");
                    ctlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append(" U ");
                    ctlBinaryExpression.Right.Accept(this);
                    CodeWriter.Append(" ] ");
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
            CodeWriter.Append(")");
        }

        /// <summary>
        ///     Visits an element of type <see cref="CtlUnaryExpression" />.
        /// </summary>
        /// <param name="ctlUnaryExpression">The <see cref="CtlUnaryExpression" /> instance that should be visited.</param>
        public override void VisitCtlUnaryExpression(CtlUnaryExpression ctlUnaryExpression)
        {
            Argument.NotNull(ctlUnaryExpression, () => ctlUnaryExpression);
            switch (ctlUnaryExpression.Operator)
            {
                case NuXmvCtlUnaryOperator.LogicalNot:
                    CodeWriter.Append("!");
                    break;
                case NuXmvCtlUnaryOperator.ExistsGlobally:
                    CodeWriter.Append("EG");
                    break;
                case NuXmvCtlUnaryOperator.ExistsNextState:
                    CodeWriter.Append("EX");
                    break;
                case NuXmvCtlUnaryOperator.ExistsFinally:
                    CodeWriter.Append("EF");
                    break;
                case NuXmvCtlUnaryOperator.ForallGlobally:
                    CodeWriter.Append("AG");
                    break;
                case NuXmvCtlUnaryOperator.ForallNext:
                    CodeWriter.Append("AX");
                    break;
                case NuXmvCtlUnaryOperator.ForallFinally:
                    CodeWriter.Append("AF");
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
            CodeWriter.Append("(");
            ctlUnaryExpression.Expression.Accept(this);
            CodeWriter.Append(")");
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlSpecification" />.
        /// </summary>
        /// <param name="ltlSpecification">The <see cref="LtlSpecification" /> instance that should be visited.</param>
        public override void VisitLtlSpecification(LtlSpecification ltlSpecification)
        {
            Argument.NotNull(ltlSpecification, () => ltlSpecification);
            //TODO allow named specifications
            CodeWriter.Append("LTLSPEC ");
            ltlSpecification.LtlExpression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlSimpleExpression" />.
        /// </summary>
        /// <param name="ltlSimpleExpression">The <see cref="LtlSimpleExpression" /> instance that should be visited.</param>
        public override void VisitLtlSimpleExpression(LtlSimpleExpression ltlSimpleExpression)
        {
            Argument.NotNull(ltlSimpleExpression, () => ltlSimpleExpression);
            ltlSimpleExpression.Expression.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlBinaryExpression" />.
        /// </summary>
        /// <param name="ltlBinaryExpression">The <see cref="LtlBinaryExpression" /> instance that should be visited.</param>
        public override void VisitLtlBinaryExpression(LtlBinaryExpression ltlBinaryExpression)
        {
            Argument.NotNull(ltlBinaryExpression, () => ltlBinaryExpression);
            
            CodeWriter.Append("(");
            switch (ltlBinaryExpression.Operator)
            {
                case NuXmvLtlBinaryOperator.LogicalAnd:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("&");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.LogicalOr:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("|");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.LogicalXor:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("xor");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.LogicalNxor:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("nxor");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.LogicalImplies:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("->");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.LogicalEquivalence:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append("<->");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.FutureUntil:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append(" U ");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.FutureReleases:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append(" R ");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.PastSince:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append(" S ");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                case NuXmvLtlBinaryOperator.PastTriggered:
                    ltlBinaryExpression.Left.Accept(this);
                    CodeWriter.Append(" T ");
                    ltlBinaryExpression.Right.Accept(this);
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
            CodeWriter.Append(")");
        }

        /// <summary>
        ///     Visits an element of type <see cref="LtlUnaryExpression" />.
        /// </summary>
        /// <param name="ltlUnaryExpression">The <see cref="LtlUnaryExpression" /> instance that should be visited.</param>
        public override void VisitLtlUnaryExpression(LtlUnaryExpression ltlUnaryExpression)
        {
            Argument.NotNull(ltlUnaryExpression, () => ltlUnaryExpression);
            switch (ltlUnaryExpression.Operator)
            {
                case NuXmvLtlUnaryOperator.LogicalNot:
                    CodeWriter.Append(" ! ");
                    break;
                case NuXmvLtlUnaryOperator.FutureNext:
                    CodeWriter.Append(" X ");
                    break;
                case NuXmvLtlUnaryOperator.FutureGlobally:
                    CodeWriter.Append(" G ");
                    break;
                case NuXmvLtlUnaryOperator.FutureFinally:
                    CodeWriter.Append(" F ");
                    break;
                case NuXmvLtlUnaryOperator.PastPrevious:
                    CodeWriter.Append(" Y ");
                    break;
                case NuXmvLtlUnaryOperator.PastNotPreviousStateNot:
                    CodeWriter.Append(" Z ");
                    break;
                case NuXmvLtlUnaryOperator.PastHistorically:
                    CodeWriter.Append(" H ");
                    break;
                case NuXmvLtlUnaryOperator.PastOnce:
                    CodeWriter.Append(" O ");
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
            CodeWriter.Append("(");
            ltlUnaryExpression.Expression.Accept(this);
            CodeWriter.Append(")");
        }

    }

    #endregion
}