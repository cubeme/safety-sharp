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

open SafetySharp.Ternary

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
        
    type FormOfGuards =
        | Unknown
        // Completely defined / left total syntactically. The syntax of the guards themselves guarantees, that every time at least one choice can be taken
        | CompletelyDefinedSyntactically
        // Completely defined / left total contextually. The assignment before guarantees that the guards of the choices are enough.
        // Example code: "x:=3; choose {x >= 2 => {}}". Pruning some guards may decrease the size of the treeified form.
        | CompletelyDefinedFromContextually
        // Completely defined and deterministic / (total) function / left total and right unique syntactically.
        // Perhaps determinism enables optimized translations if it is known which parts of the program are deterministic
        | CompletelyDefinedAndDeterministicSyntactically
        // Completely defined and deterministic / (total) function / left total and right unique contextually.
        | CompletelyDefinedAndDeterministicContextually
        // Guards are neither completely defined syntactically or contextually. Thus a statement may deadlock
        // Example code: "x:=range(1,2); choose { x == 1 => {}}"
        | MayDeadlock
        // No choice has a guard
        | CompletelyUndeterministic

    type StatementId = StatementId of int
        with
            member this.id = match this with | StatementId(value)-> value
    
    type Stm =
        | Assert of SID:StatementId * Expression:Expr       //semantics: wp( Stm.Assert(e), phi) := e && phi (formula to prove is false, when assertion is false)
        | Assume of SID:StatementId * Expression:Expr       //semantics: wp( Stm.Assume(e), phi) := e -> phi
        | Block of SID:StatementId * Statements:Stm list
        | Choice of SID:StatementId * Choices:(Expr option * Stm) list //Expr must be of type BoolVal
        | Stochastic of SID:StatementId * StochasticChoices:(Expr * Stm) list //Expr must be of type ProbVal
        | Write of SID:StatementId * Variable:Var * Expression:Expr
        //| ParallelWrite  // TODO (maybe): Parallel assignment could simplify some algorithms
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
    
    type Attributes = {
        IsStochastic : Ternary;
        IsDeterminstic : Ternary;
        AllChoicesWithoutGuards : Ternary;
        MayDeadlock : Ternary;
        HasClocks : Ternary;
        HasPhysicalValues : Ternary;
        IsSingleAssignment : Ternary;
        HasAssumptions : Ternary;
        HasAssertions : Ternary;
        SemanticsOfAssignmentToRangedVariablesAppliedExplicitly : Ternary;
    }
        with
            static member fullyUnknown =
                {
                    Attributes.IsStochastic = Ternary.Unknown;
                    Attributes.IsDeterminstic = Ternary.Unknown;
                    Attributes.AllChoicesWithoutGuards = Ternary.Unknown;
                    Attributes.MayDeadlock = Ternary.Unknown;
                    Attributes.HasClocks = Ternary.Unknown;
                    Attributes.HasPhysicalValues = Ternary.Unknown;
                    Attributes.IsSingleAssignment = Ternary.Unknown;
                    Attributes.HasAssumptions = Ternary.Unknown;
                    Attributes.HasAssertions = Ternary.Unknown;
                    Attributes.SemanticsOfAssignmentToRangedVariablesAppliedExplicitly = Ternary.Unknown;
                }

    type Pgm = {
        Globals : GlobalVarDecl list;
        Locals : LocalVarDecl list;
        VarToType: Map<Var,Type>; // Actually VarToType is only derived from Globals and Locals. But it is so useful in many cases that we introduced an own field. Maybe make it "Lazy"
        //NextGlobal maps to each global variable var_i the variable var_j, which contains the value of var_i, after Body was executed. var_i can be var_j (substitution)
        NextGlobal : Map<Var,Var>;
        CodeForm : CodeForm;
        Attributes : Attributes;
        Body : Stm;
        UniqueStatementIdGenerator : unit -> StatementId;
    }

    type Traceable = SafetySharp.Models.Sam.Traceable
                