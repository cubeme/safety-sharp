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

namespace SafetySharp.Modeling.Faults
{
	using System;
	using System.Linq;
	using System.Linq.Expressions;
	using System.Reflection;
	using CompilerServices;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a base class for all faults.
	/// </summary>
	public abstract class Fault
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		protected Fault()
		{
			MetadataProvider.CreateBuilder(this);

			OccurrencePattern = GetType().GetCustomAttribute<OccurrencePatternAttribute>();
			Requires.That(OccurrencePattern != null, "Expected fault to be marked with an instance of '{0}'.",
				typeof(OccurrencePatternAttribute).FullName);
		}

		/// <summary>
		///     Gets the fault's occurrence pattern.
		/// </summary>
		internal OccurrencePatternAttribute OccurrencePattern { get; private set; }

		/// <summary>
		///     Gets or sets a value indicating whether the fault is currently occurring.
		/// </summary>
		internal bool Occurring { get; set; }

		/// <summary>
		///     Gets the fault effects declared by the fault.
		/// </summary>
		private MethodInfo[] FaultEffects
		{
			get
			{
				return GetType()
					.GetMethods(BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.FlattenHierarchy | BindingFlags.Instance)
					.Where(m => m.DeclaringType != typeof(Fault) && m.DeclaringType != typeof(object))
					.ToArray();
			}
		}

		/// <summary>
		///     Gets the methods affected by the fault.
		/// </summary>
		private MethodInfo[] AffectedMethods
		{
			get
			{
				return GetType()
					.DeclaringType.GetMethods(BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.FlattenHierarchy | BindingFlags.Instance)
					.Where(m => m.GetCustomAttribute<ProvidedAttribute>() != null)
					.ToArray();
			}
		}

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the current fault's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		protected static void SetInitialValues<T>(T field, params T[] values)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Updates the fault's internal state.
		/// </summary>
		internal void Update()
		{
			//Occurring = OccurrencePattern.UpdateOccurrence();
		}

		/// <summary>
		///     Checks whether <paramref name="faultEffect" /> overrides the <paramref name="affectedMethod" /> candidate.
		/// </summary>
		/// <param name="faultEffect">The fault effect that should be checked.</param>
		/// <param name="affectedMethod">The affected method that should be checked.</param>
		private static bool Overrides(MethodInfo faultEffect, MethodInfo affectedMethod)
		{
			return faultEffect.Name == affectedMethod.Name &&
				   faultEffect.ReturnType == affectedMethod.ReturnType &&
				   faultEffect.GetParameters().Length == affectedMethod.GetParameters().Length &&
				   faultEffect.GetGenericArguments().Length == affectedMethod.GetGenericArguments().Length &&
				   faultEffect.GetParameters().Zip(affectedMethod.GetParameters(), (p1, p2) => p1.ParameterType == p2.ParameterType).All(b => b) &&
				   faultEffect.GetGenericArguments().Zip(affectedMethod.GetGenericArguments(), (p1, p2) => p1 == p2).All(b => b);
		}

		/// <summary>
		///     Initialize the fault for <paramref name="component" />.
		/// </summary>
		/// <param name="component">The component that should be affected by the fault.</param>
		internal void Initialize(Component component)
		{
			Requires.NotNull(component, () => component);

			var affectedMethods = AffectedMethods;
			foreach (var faultEffect in FaultEffects)
			{
				var affectedMethod = affectedMethods.SingleOrDefault(m => Overrides(faultEffect, m));
				Requires.That(affectedMethod != null, "Unable to find affected method for fault effect '{0}'.", faultEffect);

				var field = affectedMethod.GetCustomAttribute<BackingFieldAttribute>().GetFieldInfo(affectedMethod.DeclaringType);
				var faultEffectDelegate = Delegate.CreateDelegate(field.FieldType, this, faultEffect);

				var parameters = affectedMethod.GetParameters().Select(p => Expression.Parameter(p.ParameterType, p.Name)).ToArray();
				var fault = Expression.Constant(this);
				var delegateExpression = Expression.Constant(faultEffectDelegate);
				var elseDelegate = Expression.Constant(field.GetValue(component));
				var occurringGetter = typeof(Fault).GetProperty("Occurring", BindingFlags.NonPublic | BindingFlags.Instance).GetMethod;
				var isOccurring = Expression.Property(fault, occurringGetter);
				var invokeFault = Expression.Invoke(delegateExpression, parameters);
				var invokeOther = Expression.Invoke(elseDelegate, parameters);
				var body = Expression.Condition(isOccurring, invokeFault, invokeOther);
				var lambda = Expression.Lambda(field.FieldType, body, parameters);
				var compiledMethodDelegate = lambda.Compile();

				field.SetValue(component, compiledMethodDelegate);
			}
		}
	}
}