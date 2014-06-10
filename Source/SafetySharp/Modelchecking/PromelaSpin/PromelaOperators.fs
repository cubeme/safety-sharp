namespace PromelaDataStructures.Ast

type Unarop =
    | Tilde // ~
    | Neg   // -
    | Not   // !

type Andor =
    | And  // &&
    | Or   // ||
    
type Binarop =
    | Add  // +
    | Min  // -
    | Mul  // *
    | Div  // /
    | Mod  // %
    | BAnd // & (Bitwise And)
    | Xor  // ^
    | BOr  // | (Bitwise Or)
    | Gt   // >
    | Lt   // >
    | Ge   // >=
    | Le   // <=
    | Eq   // ==
    | Neq  // !=
    | Bls  // << (Bitwise left shift)
    | Brs  // >> (Bitwise left shift)
    | Andor of Andor // &&, ||