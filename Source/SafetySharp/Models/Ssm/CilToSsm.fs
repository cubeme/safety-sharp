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

namespace SafetySharp.Models

/// Transforms an unstructured CIL method body to a structured SSM statement.
/// For details on how parts of the transformation work, see the paper by D. Demange et. al, entitled
/// "A provably correct stackless intermediate representation for Java bytecode"
module internal CilToSsm =
    open SafetySharp
    open Cil
    open Ssm

    /// Generates a fresh local variable (see also the Demange paper)
    let private freshLocal pc idx =
        sprintf "__tmp_%i_%i" pc idx |> Local
    
    /// Inspects the given symbolic stack to transform the given CIL instruction to a triple
    /// of the corresponding SSM instruction, a list of assignments to temporary variables,
    /// and a new symbolic stack.
    /// This function corresponds to the BC2BIR_instr function in the Demange paper.
    let private transformInstr pc instr stack =
        // Checks whether the stack contains an expression referencing a variable that satisfies the given predicate.
        let checkStack pred stack =
            let rec check = function
                | VarExpr v -> pred v
                | UExpr (_, e) -> check e
                | BExpr (e1, _, e2) -> check e1 || check e2
                | _ -> false

            stack |> List.exists check    

        // Replaces all variable expressions referencing a variable that satisfies the given predicate.
        let replaceVar pred var stack =
            let rec replace = function
                | VarExpr v -> if pred v then VarExpr var else VarExpr v
                | UExpr (op, e) -> UExpr (op, replace e)
                | BExpr (e1, op, e2) -> BExpr (replace e1, op, replace e2)
                | e -> e

            stack |> List.map replace

        let localVarPred l = function | Local l' -> l = l' | _ -> false
        let argVarPred a = function | Arg a' -> a = a' | _ -> false
        let containsLocal l = checkStack (localVarPred l)
        let replaceLocal l = replaceVar (localVarPred l)
        let containsArg a = checkStack (argVarPred a)
        let replaceArg a = replaceVar (argVarPred a)

        // Corresponds to the tabular specification of BC2BIR_instr
        match instr, stack with
        | (Instr.Nop, s) -> (NopStm, [], s)
        | (Instr.Ldc c, s) -> (NopStm, [], (IntExpr c) :: s)
        | (Instr.Ldarg a, s) -> (NopStm, [], (VarExpr (Arg a.Name)) :: s)
        | (Instr.Ldloc l, s) -> (NopStm, [], (VarExpr (Local l.Name)) :: s)
        | (Instr.Starg a, e :: s) when not (containsArg a.Name s) -> (AsgnStm (Arg a.Name, e), [], s)
        | (Instr.Starg a, e :: s) when containsArg a.Name s -> 
            let tmp = freshLocal pc 0
            (AsgnStm (Arg a.Name, e), [AsgnStm (tmp, VarExpr (Arg a.Name))], replaceArg a.Name tmp s)
        | (Instr.Stloc l, e :: s) when not (containsLocal l.Name s) -> (AsgnStm (Local l.Name, e), [], s)
        | (Instr.Stloc l, e :: s) when containsLocal l.Name s -> 
            let tmp = freshLocal pc 0
            (AsgnStm (Local l.Name, e), [AsgnStm (tmp, VarExpr (Local l.Name))], replaceLocal l.Name tmp s)
        | (Instr.Br (Always, t), s) -> (GotoStm (BoolExpr true, t), [], s)
        | (Instr.Br (True, t), e :: s) -> (GotoStm (e, t), [], s)
        | (Instr.Br (False, t), e :: s) -> (GotoStm (UExpr (Not, e), t), [], s)
        | (Instr.Br (op, t), e1 :: e2 :: s) -> 
            let op = 
                match op with
                | BrType.Eq -> Eq
                | BrType.Ne -> Ne
                | BrType.Ge -> Ge
                | BrType.Gt -> Gt
                | BrType.Le -> Le
                | BrType.Lt -> Lt
                | _ -> invalidOp "Unsupported branch type '%+A'." op
            (GotoStm (BExpr (e2, op, e1), t), [], s)
        | (Instr.Dup, e :: s) -> (NopStm, [], e :: e :: s)
        | (Instr.And, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, And, e1)) :: s)
        | (Instr.Or, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Or, e1)) :: s)
        | (Instr.Ceq, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Eq, e1)) :: s)
        | (Instr.Cgt, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Gt, e1)) :: s)
        | (Instr.Clt, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Lt, e1)) :: s)
        | (Instr.Add, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Add, e1)) :: s)
        | (Instr.Sub, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Sub, e1)) :: s)
        | (Instr.Mul, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Mul, e1)) :: s)
        | (Instr.Div, e1 :: e2 :: s) -> (NopStm, [], (BExpr (e2, Div, e1)) :: s)
        | (Instr.Ret, e :: s) -> (RetStm (Some e), [], s)
        | (Instr.Ret, []) -> (RetStm None, [], [])
        | _ -> invalidOp "Failed to transform instruction '%+A' for stack '%+A'." instr stack

    /// Transforms all instructions of the method body to list of SSM statements with unstructured control flow.
    /// This function corresponds to the BC2BIR function in the Demange paper.
    let private transformMethod methodBody =
        let jumpTargets = getJumpTargets methodBody
        let isJumpTarget pc = Set.contains pc jumpTargets
        let succ = Cil.getSuccessors methodBody
        let outStacks = Array.zeroCreate methodBody.Length

        // Corresponds to the newStackJmp function in the Demange paper; unfortunately,
        // the paper does not describe what the function really does. From experimentation,
        // it has been inferred that the function checks that all of its predecessors 
        // have a stack of the same size and then generates a stack with a temporary
        // variable for each expression on the stack. 
        let getJumpStack pc =
            match [0..pc] |> List.filter (fun pc' -> succ pc' |> Set.contains pc) with
            | [] -> []
            | p :: preds ->
                let stackSize = List.length outStacks.[p]
                if preds |> List.exists (fun p' -> (List.length outStacks.[p']) <> stackSize) then
                    invalidOp "Invalid control flow detected: A join point can be reached with different stack sizes."
                outStacks.[p] |> List.mapi (fun idx _ -> VarExpr (freshLocal pc idx))

        // Corresponds to the TAssign function in the Demange paper; creates a fresh local
        // variable with a unique name for each element on the symbolic stack.
        let tmpAssigns pcs stack =
            pcs 
            |> Set.map (fun pc ->
                stack |> List.mapi (fun idx expr -> AsgnStm (freshLocal pc idx, expr))
            ) 
            |> List.ofSeq 
            |> List.collect id

        // Corresponds to the loop of BC2BIR
        let (_, _, stms) =
            Array.fold (fun (pc, stack, stms) instr ->
                let stack = if isJumpTarget pc then getJumpStack pc else stack
                let (stm, vars, stack') = transformInstr pc instr stack
                outStacks.[pc] <- stack'
                
                if stack' <> [] && succ pc |> Set.exists (fun pc' -> pc' < pc) then 
                    invalidOp "Invalid control flow detected: Backward jump (with non-empty stack). Loops are not supported by S#."

                let smts = stms @ [vars @ (tmpAssigns (Set.intersect (succ pc) (jumpTargets)) stack') @ [stm]]
                let stack' =  if succ pc |> Set.contains (pc + 1) && not (isJumpTarget (pc + 1)) then stack' else []
                (pc + 1, stack', smts)
            ) (0, [], []) methodBody

        stms

    /// Compresses the statement array, removing all nops. The targets of gotos are updated accordingly. This step
    /// merely simplifies debugging and is not required for the transformation to be correct.
    let private compress methodBody =
        // Associates each statement with its program counter; statements are flattened into a single
        // list, with all statements originating from the same sublist sharing the same program counter
        let flattened = 
            methodBody 
            |> List.mapi (fun pc stm -> (pc, stm))
            |> List.collect (fun (pc, stm) -> stm |> List.map (fun stm -> (pc, stm)))
        
        // Finds the updated target program counter.
        let updatedTarget pc =
            flattened |> List.fold (fun (pc', found) (idx, stm) ->
                if found then
                    (pc', true)
                elif idx >= pc && stm <> NopStm then
                    (pc', true)
                elif stm <> NopStm then
                    (pc' + 1, false)
                else
                    (pc', false)
            ) (0, false) |> fst

        flattened
        |> List.map (fun (pc, stm) ->
            match stm with
            | GotoStm (e, pc) -> GotoStm (e, updatedTarget pc)
            | stm -> stm
        )
        |> List.filter (fun stm -> stm <> NopStm)
        |> Array.ofList

    /// Transforms the given CIL method body to an SSM statement with structured control flow.
    let transform methodBody =
        methodBody
        |> transformMethod
        |> compress
        |> Ssm.replaceGotos