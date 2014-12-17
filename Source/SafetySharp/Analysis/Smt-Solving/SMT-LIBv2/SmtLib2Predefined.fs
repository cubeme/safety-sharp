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

namespace SafetySharp.Internal.SmtSolving.SmtLib2.Predefined

open SafetySharp.Internal.SmtSolving.SmtLib2.Ast

//For Convenience: Predefined Symbols in Z3 (TODO: make it depend on the theory)
type internal Smt2Predefined (theory:string) =
    // Core Theory: Source http://smtlib.cs.uiowa.edu/theories/Core.smt2 ("2010-04-17")
    member this.True  =        Symbol.Symbol("true")
    member this.False =        Symbol.Symbol("false")
    member this.Not   =        Symbol.Symbol("not")
    member this.And   =        Symbol.Symbol("and")
    member this.Or    =        Symbol.Symbol("or")
    member this.Xor   =        Symbol.Symbol("xor")
    member this.Impl  =        Symbol.Symbol("=>")
    member this.Equal =        Symbol.Symbol("=")
    member this.Dist  =        Symbol.Symbol("distinct")
    member this.Ite   =        Symbol.Symbol("ite")

    // Int theory
    member this.Add   =        Symbol.Symbol("+")
    member this.Min   =        Symbol.Symbol("-")
    member this.Mul   =        Symbol.Symbol("*")
    member this.Div   =        Symbol.Symbol("div")
    
    member this.Eq    =        Symbol.Symbol("=")
    member this.Le    =        Symbol.Symbol("<=")
    member this.Ge    =        Symbol.Symbol(">=")
    member this.Gt    =        Symbol.Symbol(">")
    member this.Lt    =        Symbol.Symbol("<")
    // Real theory