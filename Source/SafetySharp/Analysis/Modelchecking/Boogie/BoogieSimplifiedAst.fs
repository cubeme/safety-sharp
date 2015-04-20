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

namespace SafetySharp.Analysis.Modelchecking.Boogie

module internal BoogieSimplifiedAst =
    
    // From: To Goto Where No Statement Has Gone Before
    //      http://research.microsoft.com/apps/pubs/default.aspx?id=131665
    //      http://dx.doi.org/10.1007/978-3-642-15057-9_11    
    // The detailed Boogie Ast could be found in: This is Boogie 2
    //      
    // Note: No support for Method Calls or CodeExprs, yet. No havoc

    type UOp = SafetySharp.Models.Sam.UOp
    type BOp = SafetySharp.Models.Sam.BOp
    type Var = SafetySharp.Models.Sam.Var
    type Val = SafetySharp.Models.Sam.Val

    type internal Expr = // Like SafetySharp.Models.Sam.Expr but without ReadOld
        | Literal of Val
        | UExpr of Operand : Expr * Operator : UOp
        | BExpr of LeftExpression : Expr * Operator : BOp * RightExpression : Expr
        | Read of Variable : Var
    
    type ProcedureName = ProcedureName of string

    type Stm =
        | Assert of Expression:Expr       //semantics: wp( Stm.Assert(e), phi) := e && phi (formula to prove is false, when assertion is false)
        | Assume of Expression:Expr       //semantics: wp( Stm.Assume(e), phi) := e -> phi
        | Write of Variable:Var * Expression:Expr
        | Call of Callee:ProcedureName * Parameters:(Expr list)
        
    type BlockId = BlockId of string

    type Transfer =
        | Goto of BlockId list
        | Return of Expr option

    type CodeBlock = {
        BlockId : BlockId;
        Statements : Stm list;
        Transfer : Transfer;
    }

    type Type = SafetySharp.Models.Sam.Type
    type VarDecl = SafetySharp.Models.Sam.LocalVarDecl
    

    type Procedure = {
        ProcedureName : ProcedureName;
        Modifies : Var list;
        Assumes : Expr;
        // TODO: Ensures :;
        InParameters: VarDecl list;
        OutParameters: VarDecl list;
        LocalVars : VarDecl list;
        Blocks : CodeBlock list;
    }

    type Pgm = {
        GlobalVars : VarDecl list;
        Procedures : Procedure list;
    }

    type Traceable = string