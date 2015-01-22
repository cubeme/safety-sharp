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

/// Transforms an unstructured CIL method body to a structured SSM statement.
/// For details on how parts of the transformation work, see the paper by D. Demange et. al, entitled
/// "A provably correct stackless intermediate representation for Java bytecode"
module internal CilToSsm =
    open System
    open System.Collections.Generic
    open System.Collections.Immutable
    open System.IO
    open System.Reflection
    open SafetySharp
    open SafetySharp.Modeling
    open Cil
    open Ssm
    open Mono.Cecil
    open Mono.Cecil.Cil

    /// Provides an extension method that returns all methods excluding all constructors.
    type private TypeDefinition with
        member this.GetMethods () = this.Methods |> Seq.filter (fun m -> not m.IsConstructor)
    
    /// Gets the C# compatiable full name.
    let private getCSharpType (fullName : string) =
        fullName.Replace("/", ".")

    /// Computes the inheritance level of a component, i.e., the distance to the SafetySharp.Modeling.Component base class
    /// in the inheritance chain minus 1.
    let rec internal getInheritanceLevel (t : TypeDefinition) =
        if t.FullName = typeof<obj>.FullName || t.FullName = typeof<Component>.FullName then
            invalidOp "Expected a type derived from '%s'." typeof<Component>.FullName
        elif t.BaseType.FullName = typeof<obj>.FullName || t.BaseType.FullName = typeof<Component>.FullName then
            0
        else
            (getInheritanceLevel (t.BaseType.Resolve ())) + 1

    /// Returns a unique name for the given field name and inheritance level.
    let internal makeUniqueFieldName fieldName inheritanceLevel =
        sprintf "%s%s" (String ('$', inheritanceLevel)) fieldName

    /// Returns a unique name for the given method name, inheritance level and overload index.
    let internal makeUniqueMethodName methodName inheritanceLevel overloadIndex =
        sprintf "%s%s%s" (String ('$', inheritanceLevel)) methodName (String ('@', overloadIndex))

     /// Gets a unique name for the given field within the declaring type's inheritance hierarchy.
    let private getUniqueFieldName (f : FieldDefinition) =
        let level = getInheritanceLevel f.DeclaringType
        makeUniqueFieldName f.Name level

    /// Gets a unique name for the given method within the declaring type's inheritance hierarchy. Overloaded methods
    /// are also assigned unique names.
    let private getUniqueMethodName (m : MethodDefinition) =
        let level = getInheritanceLevel m.DeclaringType
        let index = 
            m.DeclaringType.GetMethods() 
            |> Seq.filter (fun m' -> m'.Name = m.Name)
            |> Seq.toList
            |> List.findIndex ((=) m)

        makeUniqueMethodName m.Name level index

    /// Generates a fresh local variable (see also the Demange paper)
    let freshLocal pc idx t =
        Local (sprintf "__tmp_%i_%i" pc idx, t)

    /// Gets the direction of a method parameter.
    let getParamDir (p : ParameterDefinition) =
        if not p.ParameterType.IsByReference then In
        elif p.ParameterType.IsByReference && p.IsOut then Out
        else InOut

    /// Tries to map the given metadata type to a S# type, if possible.
    let private tryMapType (typeRef : TypeReference) =
        let metadataType = if typeRef.IsByReference then typeRef.GetElementType().MetadataType else typeRef.MetadataType
        match metadataType with
        | MetadataType.Void    -> Some VoidType
        | MetadataType.Boolean -> Some BoolType
        | MetadataType.Int32   -> Some IntType
        | MetadataType.Double  -> Some DoubleType
        | MetadataType.Class   -> Some (ClassType (getCSharpType typeRef.FullName))
        | _                    -> None

    /// Maps the metadata type of a variable to a S# type.
    let private mapVarType typeRef =
        match tryMapType typeRef with
        | None 
        | Some VoidType -> invalidOp "Unsupported variable type '%A'." typeRef
        | Some t        -> t

    /// Maps the metadata type of a variable to a S# type.
    let private mapReturnType typeRef =
        match tryMapType typeRef with
        | None 
        | Some (ClassType _) -> invalidOp "Unsupported method return type '%A'." typeRef
        | Some t             -> t
    
    /// Creates a variable using the given constructor with the given name and type.
    let private createVar constr name typeRef =
        constr (name, mapVarType typeRef)

    /// Normalizes binary expressions where one side is of type Boolean and the other side is an integer
    /// literal such that the integer literal is replaced by the corresponding Boolean literal.
    let private normalizeIntToBool bexpr =
        match bexpr with
        | BExpr (IntExpr 0, op, e2) when Ssm.deduceType e2 = BoolType -> BExpr (BoolExpr false, op, e2)
        | BExpr (e1, op, IntExpr 0) when Ssm.deduceType e1 = BoolType -> BExpr (e1, op, BoolExpr false)
        | BExpr (IntExpr i, op, e2) when Ssm.deduceType e2 = BoolType -> BExpr (BoolExpr true, op, e2)
        | BExpr (e1, op, IntExpr i) when Ssm.deduceType e1 = BoolType -> BExpr (e1, op, BoolExpr true)
        | e -> e

    /// Inspects the given symbolic stack to transform the given CIL instruction to a triple
    /// of the corresponding SSM instruction, a list of assignments to temporary variables,
    /// and a new symbolic stack.
    /// This function corresponds to the BC2BIR_instr function in the Demange paper.
    let private transformInstr pc instr stack =
        // Checks whether the stack contains an expression referencing a variable that satisfies the given predicate.
        let checkStack pred stack =
            let rec check = function
                | VarExpr v -> pred v
                | VarRefExpr v -> pred v
                | UExpr (_, e) -> check e
                | BExpr (e1, _, e2) -> check e1 || check e2
                | _ -> false

            stack |> List.exists check    

        // Replaces all variable expressions referencing a variable that satisfies the given predicate.
        let replaceVar pred var stack =
            let rec replace = function
                | VarExpr v -> if pred v then VarExpr var else VarExpr v
                | VarRefExpr v -> VarRefExpr v
                | UExpr (op, e) -> UExpr (op, replace e)
                | BExpr (e1, op, e2) -> BExpr (replace e1, op, replace e2)
                | e -> e

            stack |> List.map replace

        // Introduces a unique temporary variable that stores the value of the given expression and replaces
        // all references to the variable on the symbolic stack with the new temporary variable
        let replaceWithTempVar pc v e replace s = 
            let tmp = freshLocal pc 0 (Ssm.getVarType v)
            (AsgnStm (v, e), [AsgnStm (tmp, VarExpr v)], replace (Ssm.getVarName v) tmp s)

        let localVarPred l = function Local (l', _) -> l = l' | _ -> false
        let argVarPred a = function Arg (a', _) -> a = a' | _ -> false
        let fieldVarPred f = function Field (f', _) -> f = f' | _ -> false

        let argName (a : ParameterDefinition) = if a.Index = -1 then "this" else a.Name
        let localName (l : VariableDefinition) = if String.IsNullOrWhiteSpace l.Name then sprintf "__loc_%i" l.Index else l.Name
        let local (l : VariableDefinition) = createVar Local (localName l) l.VariableType
        let arg (a : ParameterDefinition) = createVar Arg (argName a) a.ParameterType
        let field (f : FieldReference) = createVar Field (getUniqueFieldName (f.Resolve ())) f.FieldType

        let containsLocal l = checkStack (localVarPred (localName l))
        let containsArg a = checkStack (argVarPred a)
        let containsField f = checkStack (fieldVarPred f)

        let replaceLocal l = replaceVar (localVarPred l)
        let replaceArg a = replaceVar (argVarPred a)
        let replaceField f = replaceVar (fieldVarPred f)

        // Corresponds to the tabular specification of BC2BIR_instr
        match instr, stack with
        | (Instr.Nop, s) -> (NopStm, [], s)
        | (Instr.Ldind, (VarRefExpr v) :: s) -> (NopStm, [], (VarExpr v) :: s)
        | (Instr.Ldfld f, (VarExpr v) :: s) when Ssm.isClassType v -> (NopStm, [], (VarExpr (field f)) :: s)
        | (Instr.Ldflda f, (VarExpr v) :: s) when Ssm.isClassType v -> (NopStm, [], (VarRefExpr (field f)) :: s)
        | (Instr.Ldarg a, s) when a.ParameterType.IsByReference -> (NopStm, [], (VarRefExpr (arg a)) :: s)
        | (Instr.Ldarg a, s) -> (NopStm, [], (VarExpr (arg a)) :: s)
        | (Instr.Ldarga a, s) -> (NopStm, [], (VarRefExpr (arg a)) :: s)
        | (Instr.Ldloc l, s) -> (NopStm, [], (VarExpr (local l)) :: s)
        | (Instr.Ldloca l, s) -> (NopStm, [], (VarRefExpr (local l)) :: s)
        | (Instr.Ldci c, s) -> (NopStm, [], (IntExpr c) :: s)
        | (Instr.Ldcd c, s) -> (NopStm, [], (DoubleExpr c) :: s)
        | (Instr.Stind, e :: (VarRefExpr (Arg (a, t))) :: s) when not (containsArg a s) -> (AsgnStm (Arg (a, t), e), [], s)
        | (Instr.Stind, e :: (VarRefExpr (Arg (a, t))) :: s) -> replaceWithTempVar pc (Arg (a, t)) e replaceArg s  
        | (Instr.Stfld f, e :: (VarExpr v) :: s) when Ssm.isClassType v && not (containsField f.Name s) -> (AsgnStm (field f, e), [], s)
        | (Instr.Stfld f, e :: (VarExpr v) :: s) when Ssm.isClassType v -> replaceWithTempVar pc (field f) e replaceField s  
        | (Instr.Starg a, e :: s) when not (containsArg (argName a) s) -> (AsgnStm (arg a, e), [], s)
        | (Instr.Starg a, e :: s) when containsArg (argName a) s -> replaceWithTempVar pc (arg a) e replaceArg s  
        | (Instr.Stloc l, e :: s) when not (containsLocal l s) -> (AsgnStm (local l, e), [], s)
        | (Instr.Stloc l, e :: s) when containsLocal l s -> replaceWithTempVar pc (local l) e replaceLocal s         
        | (Instr.Call m, s) when List.length s >= m.Parameters.Count + (if m.IsStatic then 0 else 1) ->
            let argCount = m.Parameters.Count
            let returnType = mapReturnType m.ReturnType
            let paramTypes = m.Parameters |> Seq.map (fun p -> mapVarType p.ParameterType) |> Seq.toList
            let paramDirs = m.Parameters |> Seq.map getParamDir |> Seq.toList
            let args = s |> Seq.take argCount |> Seq.toList |> List.rev
            let methodId = { Type = getCSharpType m.DeclaringType.FullName; Name = getUniqueMethodName m }

            // Determine the target of invocation, if any
            let target = 
                if m.IsStatic then None 
                else match s.[m.Parameters.Count] with
                     | VarExpr v when Ssm.isClassType v && Ssm.getVarName v = "this" -> Some (VarExpr (This (ClassType (Ssm.getClassType v))))
                     | v -> Some v

            // Pop the arguments from the symbolic stack, as well as the invocation target for non-static methods
            let s = s |> Seq.skip (argCount + (if m.IsStatic then 0 else 1)) |> Seq.toList

            // Save the current value of all fields that are currently on the stack; the function that is being 
            // called might change the values of those fields
            let fields = s |> List.map Ssm.getFieldsOfExpr |> List.collect id |> Seq.distinct
            let (idx, vars, stack) = 
                fields |> Seq.fold (fun (idx, vars, s) field ->
                    let tmp = freshLocal pc idx (Ssm.getVarType field)
                    (idx + 1, (AsgnStm (tmp, VarExpr field)) :: vars, replaceField (Ssm.getVarName field) tmp s)
                ) (0, [], s)

            // We also have to save the current value of all locals and arguments that are currently on the stack if
            // those are passed by reference to the function; the function will most likely change their value
            let stackVars = stack |> List.map (Ssm.getVarsOfExpr (fun _ -> true)) |> List.collect id |> Seq.distinct |> List.ofSeq
            let (idx, vars, stack) = 
                 Seq.filter (fun a -> match a with VarRefExpr (Arg _) | VarRefExpr (Local _) -> true | _ -> false) args
                 |> Seq.map (fun a -> match a with VarRefExpr v -> v | _ -> invalidOp "Unexpected expression type.")
                 |> Seq.filter (fun a -> List.exists ((=) a) stackVars)
                 |> Seq.fold (fun (idx, vars, s) v ->
                    let tmp = freshLocal pc idx (Ssm.getVarType v)
                    (idx + 1, (AsgnStm (tmp, VarExpr v)) :: vars, replaceVar ((=) v) tmp s)
                 ) (idx, vars, stack)

            if returnType = VoidType then
                (CallStm (methodId, paramTypes, paramDirs, returnType, args, target), vars, stack)
            else
                let tmp = freshLocal pc idx returnType
                (NopStm, vars @ [AsgnStm (tmp, CallExpr (methodId, paramTypes, paramDirs, returnType, args, target))], (VarExpr tmp) :: stack)
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
            (GotoStm (normalizeIntToBool (BExpr (e2, op, e1)), t), [], s)
        | (Instr.Dup, e :: s) -> (NopStm, [], e :: e :: s)
        | (Instr.Pop, CallExpr (m, p, d, r, e, t) :: s) -> (CallStm (m, p, d, r, e, t), [], s)
        | (Instr.Pop, e :: s) -> (NopStm, [], s)
        | (Instr.And, e1 :: e2 :: s) -> (NopStm, [], (normalizeIntToBool (BExpr (e2, And, e1))) :: s)
        | (Instr.Or, e1 :: e2 :: s) -> (NopStm, [], (normalizeIntToBool (BExpr (e2, Or, e1))) :: s)
        | (Instr.Ceq, e1 :: e2 :: s) -> (NopStm, [], (normalizeIntToBool (BExpr (e2, Eq, e1))) :: s)
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
    let private transformMethodBody methodBody =
        let jumpTargets = getJumpTargets methodBody
        let isJumpTarget pc = Set.contains pc jumpTargets
        let succ = Cil.getSuccessors methodBody
        let outStacks = Array.zeroCreate methodBody.Length

        // Corresponds to the newStackJmp function in the Demange paper; unfortunately,
        // the paper does not describe what the function really does. From experimentation,
        // it has been inferred that the function checks that all of its predecessors 
        // have a stack of the same size and then generates a stack with a temporary
        // variable for each expression on the stack. 
        // Also, the function has been extended to handle references to variables: For such
        // var refs, no temporary variables are introduced; instead, we always use the 
        // actual value on the symbol stack. For that to work, we require that the same
        // var ref lies on the stack regardless of the path taken to the join point. So far,
        // the C# compiler seems to respect that limitation.
        let getJumpStack pc =
            let extractVarRefs stack =
                stack
                |> List.mapi (fun idx expr -> (idx, expr))
                |> List.filter (fun (idx, expr) -> match expr with VarRefExpr _ -> true | _ -> false)

            match [0..pc] |> List.filter (fun pc' -> succ pc' |> Set.contains pc) with
            | [] -> []
            | p :: preds ->
                let stackSize = List.length outStacks.[p]
                let varRefs = extractVarRefs outStacks.[p]
                if preds |> List.exists (fun p' -> (List.length outStacks.[p']) <> stackSize) then
                    invalidOp "Invalid control flow detected: A join point can be reached with different stack sizes."
                if preds |> List.exists (fun p' -> varRefs <> (extractVarRefs outStacks.[p'])) then
                    invalidOp "Invalid control flow detected: A join point can be reached with different var refs on the stack."
                outStacks.[p] 
                |> List.fold (fun (stack, idx) expr -> 
                    match expr with
                    | VarRefExpr v -> ((VarRefExpr v) :: stack, idx)
                    | expr         -> ((VarExpr (freshLocal pc idx (Ssm.deduceType expr))) :: stack, idx + 1)
                ) ([], 0)
                |> fst
                |> List.rev

        // Corresponds to the TAssign function in the Demange paper; creates a fresh local
        // variable with a unique name for each element on the symbolic stack (except for var refs).
        let tmpAssigns pcs stack =
            pcs 
            |> Set.map (fun pc ->
                stack 
                |> List.filter (function | VarRefExpr _ -> false | _ -> true)
                |> List.mapi (fun idx expr -> AsgnStm (freshLocal pc idx (Ssm.deduceType expr), expr))
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

                //printfn "%3i: %+A -> %+A" pc instr stack'
                let smts = stms @ [vars @ (tmpAssigns (Set.intersect (succ pc) (jumpTargets)) stack') @ [stm]]
                let stack' =  if succ pc |> Set.contains (pc + 1) && not (isJumpTarget (pc + 1)) then stack' else []
                (pc + 1, stack', smts)
            ) (0, [], []) methodBody

        stms

    /// Fixes up the CLR's handling of Booleans as integers. The CLR represents 'false' as 0 and 'true' as non-0, similar to C.
    /// It also allows implicit "conversion" of ints to bools. C# and the SSM, however, don't allow that, so we have to fix
    /// that in a couple of places.
    let private fixIntIsBool returnsBool methodBody =
        // Makes all implict conversions of ints or doubles to bool within an expression explicit
        let rec fixExpr e isBool =
            match e with
            | IntExpr 0 when isBool       -> BoolExpr false
            | IntExpr _ when isBool       -> BoolExpr true
            | CallExpr (m, p, d, r, e, t) -> CallExpr (m, p, d, r, fixCallExprs p e, t)
            | e when isBool               -> 
                match Ssm.deduceType e with
                | IntType    -> BExpr (e, Ne, IntExpr 0)
                | DoubleType -> BExpr (e, Ne, DoubleExpr 0.0)
                | _          -> e
            | e -> e

        and fixCallExprs p e =
            List.zip p e |> List.map (fun (t, e) -> fixExpr e (t = BoolType))

        // We also have to check if there is a local variable of type bool that is also defined as a local
        // of type int or double. If so, there is probably a boolean assignment of the form 'var = 0' somewhere 
        // that we have to replace with 'var = false'. Otherwise, we have no idea what might be going on and
        // simply ignore this problem, letting later steps deal with the inconsistency.
        let locals = methodBody |> Seq.map Ssm.getLocalsOfStm |> Seq.collect id |> Seq.distinct |> Seq.toList
        let shouldBeBool l =
            locals |> List.exists (function Local (l', t) when l' = l && t = BoolType -> true | _ -> false)

        Array.map (fun stm ->
            match stm with
            | NopStm -> NopStm
            | AsgnStm (Local (l, t), e) when t <> BoolType && shouldBeBool l && Ssm.deduceType e <> BoolType ->
                AsgnStm (Local (l, BoolType), fixExpr e true)
            | AsgnStm (v, e) -> AsgnStm (v, fixExpr e (Ssm.getVarType v = BoolType))
            | GotoStm (e, t) -> GotoStm (fixExpr e true, t)
            | RetStm None -> RetStm None
            | RetStm (Some e) -> RetStm (Some (fixExpr e returnsBool))
            | CallStm (m, p, d, r, e, t) -> CallStm (m, p, d, r, fixCallExprs p e, t)
            | _ -> invalidOp "Unsupported statement '%+A'." stm
        ) methodBody

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

    /// Transforms the given field value.
    let private transformFieldValue (v : obj) = 
        match v with
        | :? bool as b   -> BoolVal b
        | :? int as i    -> IntVal i
        | :? double as d -> DoubleVal d
        | _              -> invalidOp "Unsupported initial field value of type '%s'." (v.GetType().FullName)

    /// Transforms the fields of a component.
    let private transformFields (c : Component) (t : TypeDefinition) =
        t.Fields 
        |> Seq.map (fun f -> 
            match f.FieldType.MetadataType with
            | MetadataType.Boolean -> (f, Some BoolType)
            | MetadataType.Int32   -> (f, Some IntType)
            | MetadataType.Double  -> (f, Some DoubleType)
            | _                    -> (f, None)
        )
        |> Seq.filter (fun (f, t) -> t <> None)
        |> Seq.map (fun (f, t) -> { Var = Field (getUniqueFieldName f, t.Value); Init = c.GetInitialValuesOfField f |> List.map transformFieldValue })
        |> Seq.toList

    /// Transforms the given method to an SSM method with structured control flow.
    let transformMethod (m : MethodDefinition) =
        let body =
            m
            |> Cil.getMethodBody
            |> transformMethodBody
            |> compress
            |> fixIntIsBool (m.ReturnType.MetadataType = MetadataType.Boolean)
            |> Ssm.replaceGotos

        {
            Name = getUniqueMethodName m
            Body = body
            Params =
                m.Parameters 
                |> Seq.map (fun p -> { Var = Arg (p.Name, mapVarType p.ParameterType); Direction = getParamDir p })
                |> Seq.toList
            Return = mapReturnType m.ReturnType
            Locals = Ssm.getLocalsOfStm body |> Seq.distinct |> Seq.toList
            Kind = if m.RVA <> 0 then ProvPort else ReqPort
        }

    /// Transforms all methods of the given type to an SSM method with structured control flow.
    let transformMethods (t : TypeDefinition) =
        t.GetMethods()
        |> Seq.map transformMethod
        |> List.ofSeq

    /// Transforms the given component class to an SSM component, flattening the inheritance hierarchy.
    let transformType (c : Component) (t : TypeDefinition) =
        let rec transform (t : TypeDefinition) =
            let transformed =
                if t.BaseType.FullName <> typeof<obj>.FullName && t.BaseType.FullName <> typeof<Component>.FullName then
                    transform (t.BaseType.Resolve ())
                else { Name = String.Empty; Fields = []; Methods = []; Subs = [] }

            { transformed with 
                Name = t.FullName
                Fields = transformed.Fields @ (transformFields c t) 
                Methods = transformed.Methods @ (transformMethods t)
            }

        transform t

    /// Gets the type definitions for all given components.
    let getTypeDefinitions (components : Component list) =
        let dictionary = ImmutableDictionary.CreateBuilder<System.Type, TypeDefinition> ()

        components 
        |> Seq.map (fun c -> c.GetType ())
        |> Seq.distinct
        |> Seq.iter (fun t -> 
            let assemblyDefinition = AssemblyDefinition.ReadAssembly t.Assembly.Location
            dictionary.Add (t, assemblyDefinition.MainModule.Import(t).Resolve ())
        )

        dictionary.ToImmutableDictionary ()

    /// Transforms the model to a SSM model.
    let transformModel (model : Model) =
        let typeDefinitions = getTypeDefinitions model.Components

        let transform (comp : Component) =
            transformType comp typeDefinitions.[comp.GetType ()]

        model.Components |> List.map transform