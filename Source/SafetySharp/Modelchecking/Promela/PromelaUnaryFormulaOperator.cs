using System;

namespace SafetySharp.Modelchecking.Promela
{
    internal enum PromelaUnaryFormulaOperator
    {
        Not,       // !
        Always,    // []
        Eventually // <>
    }
}