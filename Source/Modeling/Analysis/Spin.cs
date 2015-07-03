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
	using AnalysisTechniques;
	using Modeling;
	using Models;
	using Utilities;

	/// <summary>
	///     Represents the SPIN model checker that can be used to thoroughly check properties of a model.
	/// </summary>
	public class Spin
	{
		private readonly AnalysisFacade _analysis = new AnalysisFacade();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="model">The model that should be checked.</param>
		public Spin(Model model)
		{
			Requires.NotNull(model, () => model);

			model.Seal();

			var transformedModel = ModelTransformation.Transform(model);
			Console.WriteLine(ScmToString.toString(transformedModel.Item));

			_analysis.setMainModel(transformedModel);
		}

		/// <summary>
		///     Checks whether the <paramref name="formula" /> holds.
		/// </summary>
		/// <param name="formula">The formula that should be checked.</param>
		public bool Check(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return _analysis.atAnalyseLtl_WithPromela(LtlFormulaTransformation.Transform(formula)).IsTrue;
		}
	}
}