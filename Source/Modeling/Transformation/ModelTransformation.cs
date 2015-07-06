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

namespace SafetySharp.Transformation
{
	using System;
	using System.Collections.Generic;
	using System.Globalization;
	using System.Linq;
	using System.Reflection;
	using Modeling;
	using Models;
	using Runtime;
	using Runtime.BoundTree;
	using Utilities;

	/// <summary>
	///   Transforms a <see cref="Model" /> instance to a <see cref="Scm.ScmModel" /> instance.
	/// </summary>
	internal static class ModelTransformation
	{
		/// <summary>
		///   Transforms the <paramref name="model" />.
		/// </summary>
		/// <param name="model">The model that should be transformed.</param>
		public static Scm.ScmModel Transform(Model model)
		{
			Requires.NotNull(model, () => model);
			return Scm.ScmModel.NewScmModel(SsmToScm.transform(SsmLowering.lower(Transform(model.Metadata.RootComponent))));
		}

		/// <summary>
		///   Transforms the <paramref name="component" /> to a <see cref="Ssm.Comp" /> instance.
		/// </summary>
		private static Ssm.Comp Transform(ComponentMetadata component)
		{
			var fields = (IEnumerable<FieldMetadata>)component.Fields;
			var methods = component.ProvidedPorts.Cast<MethodMetadata>().Concat(component.RequiredPorts).Concat(new[] { component.StepMethod });

			if (component.StateMachine != null)
			{
				var transitions = component.StateMachine.Transitions;
				methods = methods.Concat(transitions.Where(transition => transition.Guard != null).Select(transition => transition.Guard).Distinct());
				methods = methods.Concat(transitions.Where(transition => transition.Action != null).Select(transition => transition.Action).Distinct());

				fields = fields.Concat(new[] { component.StateMachine.StateField });
			}

			return Ssm.CreateComponent(GetComponentPath(component), fields.Select(Transform), methods.Select(Transform),
				component.Subcomponents.Select(Transform), component.Faults.Select(Transform), component.Bindings.Select(Transform));
		}

		/// <summary>
		///   Transforms the <paramref name="fault" />.
		/// </summary>
		private static Ssm.Fault Transform(FaultMetadata fault)
		{
			return Ssm.CreateFault(fault.Name, fault.Effects.Select(Transform));
		}

		/// <summary>
		///   Transforms the <paramref name="binding" />.
		/// </summary>
		private static Ssm.Binding Transform(BindingMetadata binding)
		{
			return new Ssm.Binding(
				GetComponentPath(binding.ProvidedPort.DeclaringObject),
				GetComponentPath(binding.RequiredPort.DeclaringObject),
				binding.ProvidedPort.Name,
				binding.RequiredPort.Name,
				Ssm.BindingKind.Instantaneous);
		}

		/// <summary>
		///   Transforms the <paramref name="method" />.
		/// </summary>
		private static Ssm.Method Transform(MethodMetadata method)
		{
			var transformation = new MethodBodyTransformation(method.DeclaringObject);
			var methodBody = method.MethodBody;
			var locals = methodBody == null ? Enumerable.Empty<Ssm.Var>() : methodBody.LocalVariables.Select(Transform);
			var body = methodBody == null ? Ssm.Stm.NopStm : transformation.TransformMethodBody(methodBody.Body);

			Ssm.MethodKind kind;
			if (method is RequiredPortMetadata)
				kind = Ssm.MethodKind.ReqPort;
			else if (method is ProvidedPortMetadata || method is GuardMetadata || method is ActionMetadata)
				kind = Ssm.MethodKind.ProvPort;
			else if (method is FaultEffectMetadata) // TODO: Fault effects for non-provided ports
				kind = Ssm.MethodKind.ProvPort;
            else
				kind = Ssm.MethodKind.Step;

			return Ssm.CreateMethod(method.Name, method.MethodInfo.GetParameters().Select(Transform), body,
				Transform(method.MethodInfo.ReturnType), locals, kind);
		}

		/// <summary>
		///   Transforms the <paramref name="parameter" />.
		/// </summary>
		private static Ssm.Param Transform(ParameterInfo parameter)
		{
			var direction = Ssm.ParamDir.In;
			if (parameter.IsOut)
				direction = Ssm.ParamDir.Out;
			else if (parameter.ParameterType.IsByRef)
				direction = Ssm.ParamDir.InOut;

			return new Ssm.Param(Ssm.Var.NewArg(parameter.Name, Transform(parameter.ParameterType)), direction);
		}

		/// <summary>
		///   Transforms the <paramref name="variable" />.
		/// </summary>
		private static Ssm.Var Transform(VariableMetadata variable)
		{
			return Ssm.Var.NewLocal(variable.Name, Transform(variable.Type));
		}

		/// <summary>
		///   Transforms the <paramref name="field" />.
		/// </summary>
		private static Ssm.Field Transform(FieldMetadata field)
		{
			var values = field.InitialValues.Select(value =>
			{
				if (field.Type == typeof(bool))
					return Ssm.InitVal.NewBoolVal((bool)value);

				if (field.Type == typeof(int))
					return Ssm.InitVal.NewIntVal((int)value);

				if (field.Type == typeof(double))
					return Ssm.InitVal.NewDoubleVal((double)value);

				if (field.Type.IsEnum)
					return Ssm.InitVal.NewIntVal(((IConvertible)value).ToInt32(CultureInfo.InvariantCulture));

				Assert.NotReached("Unsupported type '{0}'.", field.Type.FullName);
				return null;
			});

			return Ssm.CreateField(field.Name, Transform(field.Type), values);
		}

		/// <summary>
		///   Transforms the <paramref name="type" />.
		/// </summary>
		private static Ssm.Type Transform(Type type)
		{
			if (type == typeof(void))
				return Ssm.Type.VoidType;

			if (type == typeof(bool))
				return Ssm.Type.BoolType;

			if (type == typeof(int) || type.IsEnum)
				return Ssm.Type.IntType;

			if (type == typeof(double))
				return Ssm.Type.DoubleType;

			Assert.NotReached("Unsupported type '{0}'.", type.FullName);
			return null;
		}

		/// <summary>
		///   Returns a string representation of a component path leading to <paramref name="component" />.
		/// </summary>
		private static string GetComponentPath(ComponentMetadata component)
		{
			return String.Join(".", component.GetPath());
		}

		private class MethodBodyTransformation : BoundTreeVisitor
		{
			private readonly ObjectMetadata _this;
			private Ssm.Expr _expr;
			private Ssm.Stm _stm;

			public MethodBodyTransformation(ObjectMetadata currentComponent)
			{
				_this = currentComponent;
			}

			public Ssm.Stm TransformMethodBody(Statement statement)
			{
				Visit(statement);
				return _stm;
			}

			private Ssm.Expr GetTransformed(Expression expression)
			{
				Visit(expression);
				return _expr;
			}

			private Ssm.Stm GetTransformed(Statement expression)
			{
				Visit(expression);
				return _stm;
			}

			protected internal override void VisitArgumentExpression(ArgumentExpression expression)
			{
				Visit(expression.Expression);
			}

			protected internal override void VisitBinaryExpression(BinaryExpression expression)
			{
				Ssm.BOp op;
				switch (expression.Operator)
				{
					case BinaryOperator.Add:
						op = Ssm.BOp.Add;
						break;
					case BinaryOperator.Subtract:
						op = Ssm.BOp.Sub;
						break;
					case BinaryOperator.Multiply:
						op = Ssm.BOp.Mul;
						break;
					case BinaryOperator.Divide:
						op = Ssm.BOp.Div;
						break;
					case BinaryOperator.Modulo:
						op = Ssm.BOp.Mod;
						break;
					case BinaryOperator.And:
						op = Ssm.BOp.And;
						break;
					case BinaryOperator.Or:
						op = Ssm.BOp.Or;
						break;
					case BinaryOperator.Equals:
						op = Ssm.BOp.Eq;
						break;
					case BinaryOperator.NotEquals:
						op = Ssm.BOp.Ne;
						break;
					case BinaryOperator.Less:
						op = Ssm.BOp.Lt;
						break;
					case BinaryOperator.LessEqual:
						op = Ssm.BOp.Le;
						break;
					case BinaryOperator.Greater:
						op = Ssm.BOp.Gt;
						break;
					case BinaryOperator.GreaterEqual:
						op = Ssm.BOp.Ge;
						break;
					default:
						Assert.NotReached("Unsupported binary operator.");
						return;
				}

				_expr = Ssm.Expr.NewBExpr(GetTransformed(expression.LeftOperand), op, GetTransformed(expression.RightOperand));
			}

			protected internal override void VisitBooleanLiteralExpression(BooleanLiteralExpression expression)
			{
				_expr = Ssm.Expr.NewBoolExpr(expression.Value);
			}

			protected internal override void VisitConditionalExpression(ConditionalExpression expression)
			{
				throw new NotImplementedException();
			}

			protected internal override void VisitDoubleLiteralExpression(DoubleLiteralExpression expression)
			{
				_expr = Ssm.Expr.NewDoubleExpr(expression.Value);
			}

			protected internal override void VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression)
			{
				_expr = Ssm.Expr.NewIntExpr(expression.IntegerValue);
			}

			protected internal override void VisitFieldExpression(FieldExpression expression)
			{
				_expr = Ssm.Expr.NewVarExpr(Ssm.Var.NewField(expression.Field.Name, Transform(expression.Field.Type)));
			}

			protected internal override void VisitMethodInvocationExpression(MethodInvocationExpression expression)
			{
				_expr = Ssm.CreateCall(expression.Method.Name, expression.Method.MethodInfo.DeclaringType.FullName,
					expression.Method.MethodInfo.GetParameters().Select(p => Transform(p.ParameterType)),
					expression.Method.MethodInfo.GetParameters().Select(p =>
					{
						if (p.IsOut)
							return Ssm.ParamDir.Out;

						if (p.ParameterType.IsByRef)
							return Ssm.ParamDir.InOut;

						return Ssm.ParamDir.In;
					}), Transform(expression.Method.MethodInfo.ReturnType), expression.Arguments.Select(GetTransformed));

				if (expression.Method.DeclaringObject == _this)
					return;

				var component = (ComponentMetadata)expression.Method.DeclaringObject;
				var field = Ssm.Var.NewField(component.Name, Ssm.Type.NewClassType(component.GetType().FullName));
				_expr = Ssm.Expr.NewMemberExpr(field, _expr);
			}

			protected internal override void VisitIntegerLiteralExpression(IntegerLiteralExpression expression)
			{
				_expr = Ssm.Expr.NewIntExpr(expression.Value);
			}

			protected internal override void VisitUnaryExpression(UnaryExpression expression)
			{
				Ssm.UOp op;

				switch (expression.Operator)
				{
					case UnaryOperator.Minus:
						op = Ssm.UOp.Minus;
						break;
					case UnaryOperator.Not:
						op = Ssm.UOp.Not;
						break;
					default:
						Assert.NotReached("Unsupported unary operator.");
						return;
				}

				_expr = Ssm.Expr.NewUExpr(op, GetTransformed(expression.Operand));
			}

			protected internal override void VisitVariableExpression(VariableExpression expression)
			{
				if (expression.Variable.IsParameter)
					_expr = Ssm.Expr.NewVarExpr(Ssm.Var.NewLocal(expression.Variable.Name, Transform(expression.Variable.Type)));
				else
					_expr = Ssm.Expr.NewVarExpr(Ssm.Var.NewArg(expression.Variable.Name, Transform(expression.Variable.Type)));
			}

			protected internal override void VisitBlockStatement(BlockStatement statement)
			{
				_stm = Ssm.CreateBlock(statement.Statements.Select(GetTransformed));
			}

			protected internal override void VisitChoiceStatement(ChoiceStatement statement)
			{
				_stm = Ssm.CreateChoice(statement.Guards.Select(GetTransformed), statement.Statements.Select(GetTransformed));
			}

			protected internal override void VisitExpressionStatement(ExpressionStatement statement)
			{
				_stm = Ssm.Stm.NewExprStm(GetTransformed(statement.Expression));
			}

			protected internal override void VisitAssignmentStatement(AssignmentStatement statement)
			{
				_stm = Ssm.Stm.NewAsgnStm(((Ssm.Expr.VarExpr)GetTransformed(statement.AssignmentTarget)).Item, GetTransformed(statement.Expression));
			}

			protected internal override void VisitReturnStatement(ReturnStatement statement)
			{
				_stm = Ssm.CreateReturn(GetTransformed(statement.Expression));
			}
		}
	}
}