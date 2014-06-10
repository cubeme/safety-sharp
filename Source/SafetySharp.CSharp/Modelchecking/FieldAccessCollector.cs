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
namespace SafetySharp.Modelchecking
{
    using System.Collections.Immutable;
    using Metamodel;
    using Metamodel.Configurations;
    using Metamodel.Expressions;
    using Metamodel.Statements;
    using MM = Metamodel;

    internal class FieldAccessCollector : MM.MetamodelVisitor
    {
        //private asdsadsdsda ;
        public ImmutableDictionary<Metamodel.Expressions.FieldAccessExpression, Metamodel.Configurations.FieldConfiguration>.Builder MmFieldAccessExpressionToFieldConfiguration;

        private MetamodelConfiguration mm;

        private Metamodel.Configurations.FieldConfiguration CurrentFieldConfiguration;
        
        public FieldAccessCollector(MetamodelConfiguration mm)
        {
            this.mm = mm;
            MmFieldAccessExpressionToFieldConfiguration = ImmutableDictionary.CreateBuilder<Metamodel.Expressions.FieldAccessExpression, Metamodel.Configurations.FieldConfiguration>();

            foreach (var partition in mm.Partitions)
            {
                partition.Accept(this);
            }
    }


        /// <summary>
        ///     Visits an element of type <see cref="MetamodelConfiguration" />.
        /// </summary>
        /// <param name="metamodelConfiguration">The <see cref="MetamodelConfiguration" /> instance that should be visited.</param>
        public override void VisitMetamodelConfiguration(MM.MetamodelConfiguration metamodelConfiguration)
        {
            base.VisitMetamodelConfiguration(metamodelConfiguration);
        }

        /// <summary>
        ///     Visits an element of type <see cref="BinaryExpression" />.
        /// </summary>
        /// <param name="binaryExpression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
        public override void VisitBinaryExpression(BinaryExpression binaryExpression)
        {
            base.VisitBinaryExpression(binaryExpression);
        }

        /// <summary>
        ///     Visits an element of type <see cref="UnaryExpression" />.
        /// </summary>
        /// <param name="unaryExpression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
        public override void VisitUnaryExpression(UnaryExpression unaryExpression)
        {
            base.VisitUnaryExpression(unaryExpression);
        }

        /// <summary>
        ///     Visits an element of type <see cref="FieldAccessExpression" />.
        /// </summary>
        /// <param name="fieldAccessExpression">The <see cref="FieldAccessExpression" /> instance that should be visited.</param>
        public override void VisitFieldAccessExpression(FieldAccessExpression fieldAccessExpression)
        {
            //CurrentFieldConfiguration = fieldAccessExpression.Field;
            base.VisitFieldAccessExpression(fieldAccessExpression);
        }

        /// <summary>
        ///     Visits an element of type <see cref="BlockStatement" />.
        /// </summary>
        /// <param name="blockStatement">The <see cref="BlockStatement" /> instance that should be visited.</param>
        public override void VisitBlockStatement(BlockStatement blockStatement)
        {
            base.VisitBlockStatement(blockStatement);
        }

        /// <summary>
        ///     Visits an element of type <see cref="ReturnStatement" />.
        /// </summary>
        /// <param name="returnStatement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
        public override void VisitReturnStatement(ReturnStatement returnStatement)
        {
            base.VisitReturnStatement(returnStatement);
        }

        /// <summary>
        ///     Visits an element of type <see cref="GuardedCommandStatement" />.
        /// </summary>
        /// <param name="guardedCommandStatement">The <see cref="GuardedCommandStatement" /> instance that should be visited.</param>
        public override void VisitGuardedCommandStatement(GuardedCommandStatement guardedCommandStatement)
        {
            base.VisitGuardedCommandStatement(guardedCommandStatement);
        }

        /// <summary>
        ///     Visits an element of type <see cref="GuardedCommandClause" />.
        /// </summary>
        /// <param name="guardedCommandClause">The <see cref="GuardedCommandClause" /> instance that should be visited.</param>
        public override void VisitGuardedCommandClause(GuardedCommandClause guardedCommandClause)
        {
            base.VisitGuardedCommandClause(guardedCommandClause);
        }

        /// <summary>
        ///     Visits an element of type <see cref="AssignmentStatement" />.
        /// </summary>
        /// <param name="assignmentStatement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
        public override void VisitAssignmentStatement(AssignmentStatement assignmentStatement)
        {
            base.VisitAssignmentStatement(assignmentStatement);
        }

        /// <summary>
        ///     Visits an element of type <see cref="Partition" />.
        /// </summary>
        /// <param name="partition">The <see cref="Partition" /> instance that should be visited.</param>
        public override void VisitPartition(Partition partition)
        {
            partition.Component.Accept(this);
        }

        /// <summary>
        ///     Visits an element of type <see cref="ComponentConfiguration" />.
        /// </summary>
        /// <param name="componentConfiguration">The <see cref="ComponentConfiguration" /> instance that should be visited.</param>
        public override void VisitComponentConfiguration(ComponentConfiguration componentConfiguration)
        {
            //this.CurrentFieldConfiguration
        }
    }



}