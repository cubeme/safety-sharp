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

/// Defines types and functions for working with common intermediate language (CIL or MSIL) instructions.
module internal Cil =
    open Mono.Cecil
    open Mono.Cecil.Cil
    open Mono.Cecil.Rocks
    open SafetySharp

    /// Represents the condition that causes a branch to be taken.
    type BrType =
        | Always
        | True
        | False
        | Lt
        | Le
        | Gt
        | Ge
        | Eq
        | Ne

    /// Represents the CIL instructions supported by S#.
    type Instr =
        | Nop
        | Ldfld of FieldDefinition
        | Ldloc of VariableDefinition
        | Ldarg of ParameterDefinition
        | Ldc of int
        | Stfld of FieldDefinition
        | Stloc of VariableDefinition
        | Starg of ParameterDefinition
        | Call of MethodDefinition
        | Br of BrType * int
        | Ret
        | Or
        | And
        | Not
        | Ceq
        | Cgt
        | Clt
        | Neg
        | Add
        | Sub
        | Mul
        | Div
        | Rem
        | Dup
        | Pop

    /// Gets the body of the given method.
    let getMethodBody (m : MethodDefinition) =
        // Expand macro instructions such as ldloc.0 to ldloc (0)
        m.Body.SimplifyMacros ()

        // Map all instructions of the method to our own data types
        m.Body.Instructions 
        |> Seq.map (fun instr ->
            // Casts the instruction's operand to the required target type
            let getOperand () = instr.Operand :?> 'a

            // Creates a branch instruction of the given type; instead of using byte code offsets, however,
            // branch targets map to the target instruction's index in the method's instruction array
            let toBranch brType =
                Br (brType, m.Body.Instructions |> Seq.findIndex (fun instr' -> instr' = (getOperand ())))

            // Creates an instruction that has an operand
            let toInstr instrType =
                getOperand () |> instrType
            
            match instr.OpCode.Code with
            | Code.Nop      -> Nop
            | Code.Ldfld    -> toInstr  Ldfld
            | Code.Ldloc    -> toInstr  Ldloc
            | Code.Ldarg    -> toInstr  Ldarg
            | Code.Ldc_I4   -> toInstr  Ldc
            | Code.Stfld    -> toInstr  Stfld
            | Code.Stloc    -> toInstr  Stloc
            | Code.Starg    -> toInstr  Starg
            | Code.Call     -> toInstr  Call
            | Code.Callvirt -> toInstr  Call
            | Code.Br       -> toBranch Always
            | Code.Bgt      -> toBranch Gt
            | Code.Bge      -> toBranch Ge
            | Code.Ble      -> toBranch Le
            | Code.Blt      -> toBranch Lt
            | Code.Brtrue   -> toBranch True
            | Code.Brfalse  -> toBranch False
            | Code.Beq      -> toBranch Eq
            | Code.Bne_Un   -> toBranch Ne
            | Code.Ret      -> Ret
            | Code.Or       -> Or
            | Code.And      -> And
            | Code.Not      -> Not
            | Code.Ceq      -> Ceq
            | Code.Cgt      -> Cgt
            | Code.Clt      -> Clt
            | Code.Neg      -> Neg
            | Code.Add      -> Add
            | Code.Sub      -> Sub
            | Code.Mul      -> Mul
            | Code.Div      -> Div
            | Code.Rem      -> Rem
            | Code.Dup      -> Dup
            | Code.Pop      -> Pop
            | _             -> invalidOp "MSIL instruction '%A' is unsupported." instr
        ) 
        |> Array.ofSeq

    /// Gets the set of instruction program counters that are jump targets within the body of the method. 
    /// A jump target is any instruction that is the target of at least one branch instruction.
    let getJumpTargets methodBody =
        Array.fold (fun targets instr ->
            match instr with
            | Br (_, pc) -> targets |> Set.add pc
            | _ -> targets
        ) Set.empty methodBody

    /// Gets the set of instruction program counters that can be executed following the execution of the
    /// instruction at the given program counter. For non-branching instructions, the successor is always
    /// the next instruction of the method's body. Branching instructions, on the other hand, typically
    /// have more than one successor. Return instructions don't have any successor at all.
    let getSuccessors methodBody pc =
        let succs = function
            | Br (Always, pc) -> Set.singleton pc
            | Br (_, pc) -> [pc; pc + 1] |> Set.ofList
            | Ret -> Set.empty
            | _ -> pc + 1 |> Set.singleton

        // Get the successors of the instruction at the given program counter, removing 
        // the 'method end' program counter from the resulting set
        pc
        |> Array.get methodBody
        |> succs
        |> Set.remove (methodBody.Length)