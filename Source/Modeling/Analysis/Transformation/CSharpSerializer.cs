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

namespace SafetySharp.Analysis.Transformation
{
	using System;
	using System.Collections.Generic;
	using System.Globalization;
	using System.Linq;
	using System.Reflection;
	using Runtime;
	using Runtime.BoundTree;
	using Runtime.MetadataAnalyzers;
	using Utilities;

	/// <summary>
	///     Serializes S# metadata to C# code.
	/// </summary>
	public sealed class CSharpSerializer
	{
		/// <summary>
		///     The code writer that is used by the serializer.
		/// </summary>
		private readonly CodeWriter _writer = new CodeWriter();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public CSharpSerializer()
		{
		}

		/// <summary>
		///     Serializes the <paramref name="statement" />.
		/// </summary>
		/// <param name="statement">The statement that should be serialized.</param>
		public string Serialize(Statement statement)
		{
			_writer.Clear();

			var statementWriter = new StatementWriter(_writer);
			statementWriter.Visit(statement);

			return _writer.ToString();
		}

		/// <summary>
		///     Serializes the <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression that should be serialized.</param>
		public string Serialize(Expression expression)
		{
			_writer.Clear();

			var statementWriter = new StatementWriter(_writer);
			statementWriter.Visit(expression);

			return _writer.ToString();
		}

		/// <summary>
		///     Serializes the <paramref name="metadata" />.
		/// </summary>
		/// <param name="metadata">The metadata of the component that should be serialized.</param>
		public string Serialize(ComponentMetadata metadata)
		{
			_writer.Clear();

			_writer.AppendLine("using System;");
			_writer.AppendLine("using SafetySharp.Modeling;");
			_writer.AppendLine("using SafetySharp.Modeling.Faults;");
			_writer.NewLine();

			return SerializeRecursive(metadata);
		}

		/// <summary>
		///     Serializes the <paramref name="metadata" />.
		/// </summary>
		/// <param name="metadata">The metadata of the component that should be serialized.</param>
		private string SerializeRecursive(ComponentMetadata metadata)
		{
			_writer.AppendLine("public class {0} : Component", metadata.Name ?? "C");
			_writer.AppendBlockStatement(() =>
			{
				var statementWriter = new StatementWriter(_writer, metadata);

				foreach (var field in metadata.Fields)
					_writer.AppendLine("public {0} {1};", field.Type.FullName, field.Name);

				foreach (var port in metadata.RequiredPorts)
				{
					_writer.AppendLine("public extern {0} {1}({2});", ReturnType(port.MethodInfo.ReturnType), port.Name,
						String.Join(", ", port.MethodInfo.GetParameters().Select(Parameter)));
				}

				foreach (var port in metadata.ProvidedPorts)
				{
					_writer.AppendLine("public {0} {1}({2})", ReturnType(port.MethodInfo.ReturnType), port.Name,
						String.Join(", ", port.MethodInfo.GetParameters().Select(Parameter)));
					statementWriter.Visit(port.MethodBody);
				}

				_writer.AppendLine("public override void Update()");
				statementWriter.Visit(metadata.StepMethod.MethodBody);

				foreach (var subcomponent in metadata.Subcomponents)
				{
					SerializeRecursive(subcomponent);
					_writer.AppendLine("public {0} _{0} = new {0}();", subcomponent.Name);
				}

				_writer.AppendLine("public {0}()", metadata.Name ?? "C");
				_writer.AppendBlockStatement(() =>
				{
					foreach (var binding in metadata.Bindings)
						_writer.AppendLine("Bind(RequiredPorts.{0} = ProvidedPorts.{1});", binding.RequiredPort.Name, binding.ProvidedPort.Name);
				});

				foreach (var enumeration in statementWriter.Enums.Union(metadata.Fields.Where(f => f.Type.IsEnum).Select(f => f.Type)))
				{
					var values = String.Join(", ", Enum.GetValues(enumeration).Cast<object>().Select(v => v.ToString()));
					_writer.AppendLine("public enum {0} {{ {1} }}", enumeration.Name, values);
				}
			});

			return _writer.ToString();
		}

		/// <summary>
		///     Gets the string representation of the return <paramref name="type" />.
		/// </summary>
		private static string ReturnType(Type type)
		{
			if (type == typeof(void))
				return "void";

			return GetTypeName(type);
		}

		/// <summary>
		///     Gets the string representation of the <paramref name="type" />.
		/// </summary>
		private static string GetTypeName(Type type)
		{
			if (type.IsEnum)
				return type.Name;

			return type.FullName;
		}

		/// <summary>
		///     Gets the string representation of the <paramref name="parameter" />.
		/// </summary>
		private static string Parameter(ParameterInfo parameter)
		{
			var type = GetTypeName(parameter.ParameterType);
			if (parameter.ParameterType.IsByRef && parameter.IsOut)
				type = String.Format("out {0}", GetTypeName(parameter.ParameterType.GetElementType()));
			else if (parameter.ParameterType.IsByRef)
				type = String.Format("ref {0}", GetTypeName(parameter.ParameterType.GetElementType()));

			return String.Format("{0} {1}", type, parameter.Name);
		}

		/// <summary>
		///     Serializes <see cref="Statement" /> and <see cref="Expression" /> instances to C#.
		/// </summary>
		private class StatementWriter : BoundTreeVisitor
		{
			private readonly ComponentMetadata _metadata;
			private readonly CodeWriter _writer;
			public readonly HashSet<Type> Enums = new HashSet<Type>();

			public StatementWriter(CodeWriter writer, ComponentMetadata metadata = null)
			{
				_metadata = metadata;
				_writer = writer;
			}

			public void Visit(MethodBodyMetadata metadata)
			{
				_writer.AppendBlockStatement(() =>
				{
					foreach (var variable in metadata.LocalVariables)
					{
						string defaultValue = null;
						if (variable.Type == typeof(int))
							defaultValue = "0";
						if (variable.Type == typeof(double))
							defaultValue = "0.0";
						if (variable.Type == typeof(bool))
							defaultValue = "false";
						if (variable.Type.IsEnum)
						{
							defaultValue = String.Format("{0}.{1}", variable.Type.Name, Enum.GetValues(variable.Type).Cast<object>().First());
							Enums.Add(variable.Type);
						}
						_writer.AppendLine("{0} {1} = {2};", GetTypeName(variable.Type), variable.Name, defaultValue);
					}

					foreach (var s in metadata.Body.Statements)
						Visit(s);
				});
			}

			protected internal override void VisitArgumentExpression(ArgumentExpression expression)
			{
				switch (expression.RefKind)
				{
					case RefKind.None:
						break;
					case RefKind.Ref:
						_writer.Append("ref ");
						break;
					case RefKind.Out:
						_writer.Append("out ");
						break;
					default:
						throw new ArgumentOutOfRangeException();
				}

				Visit(expression.Expression);
			}

			protected internal override void VisitBinaryExpression(BinaryExpression expression)
			{
				_writer.Append("(");
				Visit(expression.LeftOperand);

				switch (expression.Operator)
				{
					case BinaryOperator.Add:
						_writer.Append(" + ");
						break;
					case BinaryOperator.Subtract:
						_writer.Append(" - ");
						break;
					case BinaryOperator.Multiply:
						_writer.Append(" * ");
						break;
					case BinaryOperator.Divide:
						_writer.Append(" / ");
						break;
					case BinaryOperator.Modulo:
						_writer.Append(" % ");
						break;
					case BinaryOperator.And:
						_writer.Append(" & ");
						break;
					case BinaryOperator.Or:
						_writer.Append(" | ");
						break;
					case BinaryOperator.Equals:
						_writer.Append(" == ");
						break;
					case BinaryOperator.NotEquals:
						_writer.Append(" != ");
						break;
					case BinaryOperator.Less:
						_writer.Append(" < ");
						break;
					case BinaryOperator.LessEqual:
						_writer.Append(" <= ");
						break;
					case BinaryOperator.Greater:
						_writer.Append(" > ");
						break;
					case BinaryOperator.GreaterEqual:
						_writer.Append(" >= ");
						break;
					default:
						throw new ArgumentOutOfRangeException();
				}

				Visit(expression.RightOperand);
				_writer.Append(")");
			}

			protected internal override void VisitBooleanLiteralExpression(BooleanLiteralExpression expression)
			{
				_writer.Append("{0}", expression.Value.ToString().ToLower());
			}

			protected internal override void VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression)
			{
				Enums.Add(expression.Value.GetType());
				_writer.Append("{0}.{1}", expression.Value.GetType().Name, expression.Value);
			}

			protected internal override void VisitConditionalExpression(ConditionalExpression expression)
			{
				_writer.Append("(");
				Visit(expression.Condition);
				_writer.Append(" ? ");
				Visit(expression.TrueBranch);
				_writer.Append(" : ");
				Visit(expression.FalseBranch);
				_writer.Append(")");
			}

			protected internal override void VisitDoubleLiteralExpression(DoubleLiteralExpression expression)
			{
				_writer.Append("{0}", expression.Value.ToString(CultureInfo.InvariantCulture));
			}

			protected internal override void VisitFieldExpression(FieldExpression expression)
			{
				WriteMemberAccess((ComponentMetadata)expression.Field.DeclaringObject);
				_writer.Append("{0}", expression.Field.Name);
			}

			protected internal override void VisitIntegerLiteralExpression(IntegerLiteralExpression expression)
			{
				_writer.Append("{0}", expression.Value.ToString(CultureInfo.InvariantCulture));
			}

			protected internal override void VisitUnaryExpression(UnaryExpression expression)
			{
				switch (expression.Operator)
				{
					case UnaryOperator.Minus:
						_writer.Append("-");
						break;
					case UnaryOperator.Not:
						_writer.Append("!");
						break;
					default:
						throw new ArgumentOutOfRangeException();
				}

				_writer.Append("(");
				Visit(expression.Operand);
				_writer.Append(")");
			}

			protected internal override void VisitExpressionStatement(ExpressionStatement statement)
			{
				Visit(statement.Expression);
				_writer.AppendLine(";");
			}

			protected internal override void VisitMethodInvocationExpression(MethodInvocationExpression expression)
			{
				WriteMemberAccess((ComponentMetadata)expression.Method.DeclaringObject);
				_writer.Append("{0}(", expression.Method.Name);
				_writer.AppendSeparated(expression.Arguments, ", ", Visit);
				_writer.Append(")");
			}

			protected internal override void VisitVariableExpression(VariableExpression expression)
			{
				_writer.Append("{0}", expression.Variable.Name);
			}

			protected internal override void VisitBlockStatement(BlockStatement statement)
			{
				_writer.AppendBlockStatement(() =>
				{
					foreach (var s in statement.Statements)
						Visit(s);
				});
			}

			protected internal override void VisitChoiceStatement(ChoiceStatement statement)
			{
				Requires.That(statement.IsDeterministic, "Unsupported nondeterministic choice.");

				for (var i = 0; i < statement.Guards.Count; ++i)
				{
					if (i == 0)
					{
						_writer.Append("if (");
						Visit(statement.Guards[i]);
						_writer.Append(")");
					}
					else if (i == statement.Guards.Count - 1 && statement.IsDeterministic)
						_writer.Append("else");
					else
					{
						_writer.Append("else if (");
						Visit(statement.Guards[i]);
						_writer.Append(")");
					}

					_writer.NewLine();
					Visit(statement.Statements[i]);
				}
			}

			protected internal override void VisitAssignmentStatement(AssignmentStatement statement)
			{
				Visit(statement.AssignmentTarget);
				_writer.Append(" = ");
				Visit(statement.Expression);
				_writer.AppendLine(";");
			}

			protected internal override void VisitReturnStatement(ReturnStatement statement)
			{
				if (statement.Expression == null)
					_writer.AppendLine("return;");
				else
				{
					_writer.Append("return ");
					Visit(statement.Expression);
					_writer.AppendLine(";");
				}
			}

			private void WriteMemberAccess(ComponentMetadata component)
			{
				if (component == _metadata)
					_writer.Append("this.");
				else
				{
					WriteMemberAccess(component.ParentComponent);
					_writer.Append("_{0}.", component.Name);
				}
			}
		}
	}
}