using System;

namespace SafetySharp.Modelchecking.Promela
{
    internal enum PromelaBinaryFormulaOperator
    {
        Equals,     // == <->
        Until,      // U
        WeakUntil,  // W
        Release,    // V (the dual of U): (p V q) means !(!p U !q))
        And,        // && /\
        Or,         // || \/
        Implies     // maybe equivalent to <=
    }
}