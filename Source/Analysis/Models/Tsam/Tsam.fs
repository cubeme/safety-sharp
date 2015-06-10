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

namespace SafetySharp.Models

module internal Tsam =
    // Both the transformation with weakest precondition or strongest postcondition work with a modified Sam-Model.
    
    // every statement also has a statement id = SID
    // TODO: This model also contains a notion of versions for variables.

    // Advantages of this modified Sam-Model:
    //  * Peekhole optimizations are easier.
    //  * Transformation to verification condition is slightly easier.
    // See
    //  * Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions. http://dx.doi.org/10.1145/360204.360220
    //  * Greg Nelson. A generalization of Dijkstra's calculus. http://dx.doi.org/10.1145/69558.69559

    type UOp = SafetySharp.Models.Sam.UOp
    type BOp = SafetySharp.Models.Sam.BOp
    type Var = SafetySharp.Models.Sam.Var
    type OverflowBehavior = SafetySharp.Modeling.OverflowBehavior
    type Val = SafetySharp.Models.Sam.Val
    type Expr = SafetySharp.Models.Sam.Expr
    
    type StatementId = StatementId of int
        with
            member this.id = match this with | StatementId(value)-> value
    
    type Stm =
        | Assert of SID:StatementId * Expression:Expr       //semantics: wp( Stm.Assert(e), phi) := e && phi (formula to prove is false, when assertion is false)
        | Assume of SID:StatementId * Expression:Expr       //semantics: wp( Stm.Assume(e), phi) := e -> phi
        | Block of SID:StatementId * Statements:Stm list
        | Choice of SID:StatementId * Choices:Stm list
        | Stochastic of SID:StatementId * (Expr * Stm) list //Expr must be of type ProbVal
        | Write of SID:StatementId * Variable:Var * Expression:Expr
        with
            member this.GetStatementId : StatementId =
                match this with
                    | Assert (sid,_) -> sid
                    | Assume (sid,_) -> sid
                    | Block (sid,_) -> sid
                    | Choice (sid,_) -> sid
                    | Stochastic (sid,_) -> sid
                    | Write (sid,_,_) -> sid
    
    type Type = SafetySharp.Models.Sam.Type
    type GlobalVarDecl = SafetySharp.Models.Sam.GlobalVarDecl
    type LocalVarDecl = SafetySharp.Models.Sam.LocalVarDecl
    
    [<RequireQualifiedAccessAttribute>]
    type CodeForm =
        | Default
        | SingleAssignments
        | Passive
        
    type UsedFeatures = unit
    (*{
        Indeterminism : bool;
        Probabilism : bool;
        Clocks : bool;
    }*)

    type Pgm = {
        Globals : GlobalVarDecl list;
        Locals : LocalVarDecl list;
        //NextGlobal maps to each global variable var_i the variable var_j, which contains the value of var_i, after Body was executed. var_i can be var_j (substitution)
        NextGlobal : Map<Var,Var>;
        CodeForm : CodeForm;
        UsedFeatures : UsedFeatures;
        Body : Stm;
        UniqueStatementIdGenerator : unit -> StatementId;
    }

    type Traceable = SafetySharp.Models.Sam.Traceable
                