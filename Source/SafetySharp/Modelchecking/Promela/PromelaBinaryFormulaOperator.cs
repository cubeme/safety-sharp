using System;

namespace SafetySharp.Modelchecking.Promela
{
    internal enum PromelaBinaryFormulaOperator
    {
        And,  // &&
        Or,   // ||
        Add,  // +
        Min,  // -
        Mul,  // *
        Div,  // /
        Mod,  // %
        BAnd, // & (Bitwise And)
        Xor,  // ^
        BOr,  // | (Bitwise Or)
        Gt,   // >
        Lt,   // >
        Ge,   // >=
        Le,   // <=
        Eq,   // ==
        Neq,  // !=
        Bls,  // << (Bitwise left shift)
        Brs   // >> (Bitwise left shift)
    }
}