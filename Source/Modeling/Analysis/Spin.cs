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

namespace SafetySharp.Analysis
{
	using System;
	using System.Linq;
	using AnalysisTechniques;
	using Modeling;
	using Models;
	using Transformation;
	using Utilities;

	/// <summary>
	///     Represents the SPIN model checker that can be used to thoroughly check properties of a model.
	/// </summary>
	public class Spin
	{
		private readonly AnalysisContext _analysis;
		private readonly Model _model;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="model">The model that should be checked.</param>
		public Spin(Model model)
		{
			Requires.NotNull(model, () => model);

			_model = model;
			_model.Seal();

			var transformedModel = ModelTransformation.Transform(_model);
			Console.WriteLine(ScmToString.ToString(transformedModel.Item));

			_analysis = new AnalysisContext(transformedModel);
		}

		/// <summary>
		///     Checks whether the <paramref name="formula" /> holds.
		/// </summary>
		/// <param name="formula">The formula that should be checked.</param>
		public bool Check(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return _analysis.AnalyzeWithPromela(LtlFormulaTransformation.Transform(formula));
		}

		/// <summary>
		///     Computes the minimal critical sets for the <paramref name="hazard" />.
		/// </summary>
		/// <param name="hazard">The hazard the minimal critical sets should be computed for.</param>
		public void ComputeMinimalCriticalSets(LtlFormula hazard)
		{
			Requires.NotNull(hazard, () => hazard);
			Requires.That(!hazard.Formula.IsTemporal, "The hazard must be a non-temporal formula.");

			var transformedFormula = LtlFormulaTransformation.Transform(hazard);
			var propositionalFormula = ScmVerificationElements.ToPropositionalFormula(transformedFormula);

			var minimalCriticalSets = _analysis.DccaWithPromela(propositionalFormula);
			foreach (var minimalCriticalSet in minimalCriticalSets)
			{
				Console.Write("{ ");

				foreach (var fault in minimalCriticalSet)
				{
					var component = String.Join(", ", fault.Item1.Reverse());
					Console.WriteLine("{0}.{1}", component, fault.Item2);
				}

				Console.WriteLine(" }");
			}
		}
	}
}