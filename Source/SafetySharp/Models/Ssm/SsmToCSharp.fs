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

module internal SsmToCSharp =
    open SafetySharp
    open SafetySharp.Models.Ssm

    /// Transforms the given SSM method to C# code.
    let transform m =
        let writer = StructuredWriter ()

        let varType = function
            | BoolType   -> writer.Append "bool"
            | IntType    -> writer.Append "int"
            | DoubleType -> writer.Append "double"
            | ClassType  -> writer.Append "object"

        let uop = function
            | Not   -> writer.Append "!"
            | Minus -> writer.Append "-"
     
        let bop = function
            | Add -> writer.Append "+"
            | Sub -> writer.Append "-"
            | Mul -> writer.Append "*"
            | Div -> writer.Append "/"
            | Mod -> writer.Append "%%"
            | Gt  -> writer.Append ">"
            | Ge  -> writer.Append ">="
            | Lt  -> writer.Append "<"
            | Le  -> writer.Append "<="
            | Eq  -> writer.Append "=="
            | Ne  -> writer.Append "!="
            | And -> writer.Append "&"
            | Or  -> writer.Append "|"

        let var = function
            | Arg (a, _)   -> writer.Append "%s" a
            | Local (l, _) -> writer.Append "%s" l
            | Field (f, _) -> writer.Append "%s" f

        let varDecl = function
            | Arg (a, t)   -> varType t; writer.Append " %s" a
            | Local (l, t) -> varType t; writer.Append " %s" l
            | Field (f, t) -> varType t; writer.Append " %s" f

        let rec expr = function
            | BoolExpr b         -> writer.Append <| if b then "true" else "false"
            | IntExpr i          -> writer.Append "%i" i
            | DoubleExpr d       -> writer.Append "%f" d
            | VarExpr v          -> var v
            | VarRefExpr v       -> writer.Append "&"; var v
            | UExpr (op, e)      -> uop op; writer.AppendParenthesized (fun () -> expr e)
            | BExpr (e1, op, e2) -> writer.AppendParenthesized (fun () -> expr e1; writer.Append " "; bop op; writer.Append " "; expr e2)

        let rec toCSharp stm = 
            match stm with
            | NopStm                 -> ()
            | AsgnStm (v, e)         -> 
                var v
                writer.Append " = "
                expr e
                writer.AppendLine ";"
            | GotoStm _              -> invalidOp "'goto' statements are not supported when generating C# code."
            | SeqStm s               -> s |> List.iter toCSharp
            | RetStm None            -> writer.AppendLine "return;"
            | RetStm (Some e)        -> writer.Append "return "; expr e; writer.AppendLine(";")
            | IfStm (e, s, None)     -> 
                writer.Append "if "
                writer.AppendParenthesized (fun () -> expr e)
                writer.AppendBlockStatement (fun () -> toCSharp s)
            | IfStm (e, s1, Some s2) -> 
                writer.Append "if "
                writer.AppendParenthesized (fun () -> expr e)
                writer.AppendBlockStatement (fun () -> toCSharp s1)
                writer.Append "else"
                writer.AppendBlockStatement (fun () -> toCSharp s2)
        
        match m.Return with
        | None -> writer.Append "void"
        | Some t -> varType t

        writer.Append " %s(" m.Name
        writer.AppendRepeated m.Params (fun p ->
            if p.InOut then writer.Append "ref "
            varDecl p.Var
        ) (fun () -> writer.Append ", ")
        writer.Append ")"
        writer.AppendBlockStatement (fun () -> 
            m.Locals |> List.iter (fun var -> varDecl var; writer.AppendLine ";")
            if not <| List.isEmpty m.Locals then writer.NewLine ()

            toCSharp m.Body
        )
        writer.ToString ()