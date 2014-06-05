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

namespace SafetySharp.Modeling
{
	using System;
	using System.IO;
	using CSharp;
	using CSharp.Transformation;
	using Metamodel;
	using Modelchecking.Promela;

	/// <summary>
	/// 
	/// </summary>
	public sealed class SpinModelChecker
	{
		private readonly ModelingCompilation _compilation;
		private readonly ComponentResolver _componentResolver;
		private readonly MetamodelResolver _metamodelResolver;
		private readonly SymbolMap _symbolMap;

		/// <summary>
		/// 
		/// </summary>
		/// <param name="modelConfiguration"></param>
		public SpinModelChecker(ModelConfiguration modelConfiguration)
		{
			var modelingAssembly = new ModelingAssembly(modelConfiguration.GetType().Assembly);
			var transformation = new MetamodelTransformation(modelingAssembly.Compilation, modelConfiguration.GetSnapshot());

			MetamodelCompilation compilation;
			MetamodelConfiguration configuration;
			transformation.TryTransform(out compilation, out configuration, out _symbolMap, out _componentResolver);

			_compilation = modelingAssembly.Compilation;
			_metamodelResolver = compilation.Resolver;

			var promelaTransformation = new MetamodelToPromela(configuration, compilation.Resolver);
			var promelaModel = promelaTransformation.ConvertMetaModelConfiguration();

			var promelaWriter = new PromelaModelWriter();
			promelaWriter.Visit(promelaModel);

			var fileName = modelConfiguration.GetType().Name + ".pml";
			File.WriteAllText(fileName, promelaWriter.CodeWriter.ToString());

			var result = Spin.ExecuteSpin("-a " + fileName);

			return;
		}

		/// <summary>
		/// 
		/// </summary>
		/// <param name="formula"></param>
		/// <returns></returns>
		public bool Check(LtlFormula formula)
		{
			var formulaTransformation = new FormulaTransformation(_compilation, _symbolMap, _componentResolver, _metamodelResolver);
			var transformedFormula = formulaTransformation.Visit(formula.Formula);

			return true;
		}
	}
}