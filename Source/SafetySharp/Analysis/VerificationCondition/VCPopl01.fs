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

namespace SafetySharp.Analysis.VerificationCondition

// Implementation of
//  * Cormac Flanagan, James Saxe. Avoiding Exponential Explosion: Generating Compact Verification Conditions. http://dx.doi.org/10.1145/360204.360220

// Advantage of this algorithm:
//   * smaller formulas
//   * seems to be faster for Sat/SMT-Solvers
//   * easier to verify interactively
// Disadvantages of this algorithm:
//   * more variables (artificial variables get introduced)


module internal VCPopl01 =
    open SamModified
        
    type Substitutions =
        {
            IsBottom : bool;
            CurrentSubstitution : Map<Var,Var>;
            LocalTakenNames : Set<string>;
            VarToType : Map<Var,Type>;
            GlobalTakenNames : Map<Var,Type> ref; //the set, where ref points to, stays the same, when copied. No need to merge here!
            TryToRecycle : bool; // if true, we try to recycle currently unused variables
        }
            with
                static member initial (localAndGlobalVars:Var list) =
                    {
                        Substitutions.IsBottom = false;
                        Substitutions.CurrentSubstitution =
                            localAndGlobalVars |> List.map (fun var -> (var,var))
                                               |> Map.ofList;
                    }
                static member bottom =
                    {
                        Substitutions.IsBottom = true;
                        Substitutions.CurrentSubstitution = Map.empty<Var,Var>;
                    }
                member this.tryToRecycleVar (_type:Type)=
                    ""
                    // Recycled variables are variables, which have been used before in another indeterministic choice branch.
                    // We could try to get one of these to keep the state space small. This may or may not help to reduce the
                    // verification.
                member this.getFreshVar (var:Var) : (Substitutions*Var) =
                    ""
                static member merge (subs:Substitutions list) : (Substitutions * (Stm list)) =
                    // merge is only possible, when the ref cells of GlobalTakenNames match
                    ()
    
    let rec replaceVarsWithCurrentVars (sigma:Substitutions) (expr:Expr) : Expr =
        if sigma.IsBottom then
            expr
        else
            match expr with
                | Expr.Literal (_val) -> expr
                | Expr.Read (_var) -> Expr.Read(sigma.CurrentSubstitution.Item _var)
                | Expr.ReadOld (_var) -> expr //old variables keep their value
                | Expr.UExpr (expr,uop) -> Expr.UExpr(replaceVarsWithCurrentVars sigma expr ,uop)
                | Expr.BExpr (left, bop, right) -> Expr.BExpr(replaceVarsWithCurrentVars sigma left,bop,replaceVarsWithCurrentVars sigma right)
        
    
    let rec passify (sigma:Substitutions, stm:Stm) : (Substitutions*Stm) =
        match stm with
            | Stm.Assert (expr) ->
                let expr = replaceVarsWithCurrentVars sigma expr //need to do it with old sigma!
                if expr = Expr.Literal(Val.BoolVal(false)) then
                    (Substitutions.bottom,stm) //optimization: if false, then bottom
                else
                    (sigma,stm)
            | Stm.Assume (expr) ->
                let expr = replaceVarsWithCurrentVars sigma expr  //need to do it with old sigma!
                if expr = Expr.Literal(Val.BoolVal(false)) then
                    (Substitutions.bottom,stm) //optimization: if false, then bottom
                else
                    (sigma,stm)
            | Stm.Write (variable,expression) ->
                let expr = replaceVarsWithCurrentVars sigma expression  //need to do it with old sigma!
                let newSigma,newVar = sigma.getFreshVar variable
                (newSigma,Stm.Assume(Expr.BExpr(Expr.Read(newVar),BOp.Equals,expr)))
            | Stm.Block (statements) ->
                let newSigma,statementsRev =
                    let foldFct (sigma:Substitutions,statements:Stm list) (stm:Stm) =
                        let (newSigma,newStm) = passify (sigma,stm)
                        (newSigma,newStm::statements)
                    List.fold foldFct (sigma,[]) statements
                (newSigma,Stm.Block(List.rev statementsRev))
            | Stm.Choice (choices) ->
                let (sigmas,passifiedChoices) =
                    choices |> List.map (fun choice -> passify (sigma,choice))
                            |> List.unzip
                let (newSigma,stmtsToAppend) = Substitutions.merge sigmas
                let newChoices =
                    List.map2 (fun passifiedChoice stmToAppend -> Stm.Block([passifiedChoice;stmToAppend])) passifiedChoices stmtsToAppend
                (newSigma,Stm.Choice (newChoices))
                


    (*
    type SmallRefExampel =
        {
            Local : int;
            Global : int ref;
        }
            with
                static member init =
                    {
                        SmallRefExampel.Local = 1;
                        SmallRefExampel.Global = ref(1);
                    }
                member this.increase =
                    this.Global := (!this.Global + 1);
                    { this with
                        SmallRefExampel.Local = this.Local + 1;
                    }
    let a1 = SmallRefExampel.init
    let a2 = a1
    let  b =  SmallRefExampel.init
    let  b' = b.increase
    let a1' = a1.increase
    let a2' = a1.increase
    printfn "%A" a1
    printfn "%A" a2
    printfn "%A" b
    printfn "%A" a1'
    printfn "%A" a2'
    printfn "%A" b'
    *)