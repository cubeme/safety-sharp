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

module internal ScmToString =
    open SafetySharp
    open SafetySharp.Models.Scm

    /// Gets a string representation of the given SCM model.
    let toString (c : CompDecl) =
        let writer = StructuredWriter ()

        let typeRef = function
            | BoolType    -> writer.Append "bool"
            | IntType     -> writer.Append "int"

        let uop = function
            | Not   -> writer.Append "!"
            | Minus -> writer.Append "-"
     
        let bop = function
            | Add           -> writer.Append "+"
            | Subtract      -> writer.Append "-"
            | Multiply      -> writer.Append "*"
            | Divide        -> writer.Append "/"
            | Modulo        -> writer.Append "%%"
            | Greater       -> writer.Append ">"
            | GreaterEqual  -> writer.Append ">="
            | Less          -> writer.Append "<"
            | LessEqual     -> writer.Append "<="
            | Equals        -> writer.Append "=="
            | NotEquals     -> writer.Append "!="
            | And           -> writer.Append "&&"
            | Or            -> writer.Append "||"

        let value = function
            | BoolVal b -> writer.Append "%b" b
            | IntVal i  -> writer.Append "%d" i

        let var (Var v)           = writer.Append "%s" v
        let field (Field f)       = writer.Append "%s" f
        let fault (Scm.Fault f)   = writer.Append "%s" f
        let reqPort (ReqPort r)   = writer.Append "%s" r
        let provPort (ProvPort p) = writer.Append "%s" p
        let comp (Comp c)         = writer.Append "%s" c

        let rec expr = function
            | Literal l           -> value l
            | ReadVar v           -> var v
            | ReadField f         -> field f
            | UExpr (e, op)       -> uop op; writer.AppendParenthesized (fun () -> expr e)
            | BExpr (e1, op, e2)  -> writer.AppendParenthesized (fun () -> expr e1; writer.Append " "; bop op; writer.Append " "; expr e2)

        let rec fexpr = function 
            | Fault f -> fault f
            | NotFault f -> writer.Append "!"; writer.AppendParenthesized (fun () -> fexpr f)
            | AndFault (f1, f2) -> writer.AppendParenthesized (fun () -> fexpr f1; writer.Append " && "; writer.Append " "; fexpr f2)
            | OrFault (f1, f2) -> writer.AppendParenthesized (fun () -> fexpr f1; writer.Append " || "; writer.Append " "; fexpr f2)

        let param = function
            | ExprParam e       -> writer.Append "in "; expr e
            | InOutVarParam v   -> writer.Append "inout "; var v
            | InOutFieldParam f -> writer.Append "inout "; field f

        let rec stms s = 
            s |> List.iter (fun s -> stm s; writer.NewLine ())

        and stm = function
            | AssignVar (v, e) -> var v; writer.Append " = "; expr e; writer.Append ";"
            | AssignField (f, e) -> field f; writer.Append " = "; expr e; writer.Append ";"
            | AssignFault (f, e) -> fault f; writer.Append " = "; expr e; writer.Append ";"
            | Block s -> writer.AppendBlockStatement (fun () -> stms s)
            | Choice c -> 
                writer.AppendLine "choice"
                writer.AppendBlockStatement (fun () ->
                    writer.AppendRepeated c (fun (e, s) -> 
                        expr e
                        writer.Append " => "
                        match s with
                        | Block _ -> stm s
                        | s       -> writer.Append "{ "; stm s; writer.Append " }"
                    ) (fun () -> writer.NewLine ())
                )
            | CallPort (r, p) -> 
                reqPort r
                writer.AppendParenthesized (fun () -> writer.AppendRepeated p param (fun () -> writer.Append ", "))
                writer.Append ";"
            | StepComp c -> comp c; writer.Append "();"
            | StepFault f -> fault f; writer.Append "();"

        let varDecl (v : VarDecl) =
            var v.Var
            writer.Append " : "
            typeRef v.Type

        let fieldDecl (f : FieldDecl) =
            field f.Field
            writer.Append " : "
            typeRef f.Type
            writer.Append " = "
            writer.AppendRepeated f.Init value (fun () -> writer.Append ", ")
            writer.AppendLine ";"

        let behavior (b : BehaviorDecl) = 
            writer.AppendBlockStatement (fun () ->
                b.Locals |> List.iter (fun v -> varDecl v; writer.AppendLine ";")
                match b.Body with
                | Block s -> stms s // Avoids an unnecessary pair of { }
                | s -> stm s
            )

        let paramDir = function
            | In    -> writer.Append "in"
            | InOut -> writer.Append "inout"

        let paramDecl (p : ParamDecl) = 
            paramDir p.Dir; writer.Append " "; varDecl p.Var

        let reqPortDecl (r : ReqPortDecl) =
            reqPort r.ReqPort
            writer.AppendParenthesized (fun () -> writer.AppendRepeated r.Params paramDecl (fun () -> writer.Append ", "))
            writer.AppendLine ";"

        let provPortDecl (p : ProvPortDecl) =
            match p.FaultExpr with
            | None -> ()
            | Some f -> writer.Append "["; fexpr f; writer.AppendLine "]"
            provPort p.ProvPort
            writer.AppendParenthesized (fun () -> writer.AppendRepeated p.Params paramDecl (fun () -> writer.Append ", "))
            behavior p.Behavior

        let compPath (p : CompPath) =
            writer.AppendRepeated (p |> List.rev) comp (fun () -> writer.Append ".")

        let bndSrc (b : BndSrc) =
            compPath b.Comp; writer.Append "."; provPort b.ProvPort

        let bndTarget (b : BndTarget) =
            compPath b.Comp; writer.Append "."; reqPort b.ReqPort
            
        let bndKind = function
            | Instantaneous -> writer.Append "instantly"   
            | Delayed       -> writer.Append "delayed"

        let bndDecl (b : BndDecl) =
            bndTarget b.Target
            writer.Append " = "
            bndKind b.Kind
            writer.Append " "
            bndSrc b.Source
            writer.AppendLine ";"

        let faultDecl (f : FaultDecl) = 
            writer.Append "fault "
            fault f.Fault
            writer.AppendBlockStatement (fun () -> writer.Append "step"; behavior f.Step)

        let stepDecl (s : StepDecl) = 
            match s.FaultExpr with
            | None -> ()
            | Some f -> writer.Append "["; fexpr f; writer.AppendLine "]"
            writer.Append "step"
            behavior s.Behavior

        let rec compDecl (c : CompDecl) = 
            writer.Append "component "
            comp c.Comp

            let append printer elements comment previous singleLine =
                if previous |> List.isEmpty |> not then writer.NewLine ()
                if elements |> List.isEmpty |> not then 
                    writer.AppendLine "// -------------------------"
                    writer.AppendLine "// %s" comment
                    writer.AppendLine "// -------------------------"
                    writer.AppendRepeated elements printer (fun () -> if not singleLine then writer.NewLine ())

            writer.AppendBlockStatement (fun () ->
                append compDecl c.Subs "subcomponents" [] false
                append fieldDecl c.Fields "fields" c.Subs true
                append faultDecl c.Faults "faults" c.Fields false
                append reqPortDecl c.ReqPorts "required ports" c.Faults true
                append provPortDecl c.ProvPorts "provided ports" c.ReqPorts false
                append bndDecl c.Bindings "bindings" c.ProvPorts true
                append stepDecl c.Steps "steps" c.Bindings false
            )

        compDecl c
        writer.ToString ()