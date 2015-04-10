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

namespace SafetySharp.Analysis.Modelchecking.PromelaSpin

open System

type internal PromelaToString () =

    let indent (number:int) : string =
        let s=System.Text.StringBuilder ()
        for i = 1 to number do 
            s.Append "  " |> ignore
        s.ToString ()

    let nl = Environment.NewLine
    
    let nli (i:int) =
        nl + (indent i)

    // printOptionalArgument uses the function "exporter" on the argument "opt" if "opt" is available and outputs the result. Otherwise it outputs the empty string ""
    // Example:
    //    Assume this.ExportPriority operates on an "unboxed" Priority-Value and outputs a String
    //    The following function operates on "boxed" Priority-Values (Priority option) and outputs the result of the this.ExportPriority and adds two whitespaces around the result
    //       let printPriority (priority : Priority option) : String = printOptionalArgument priority (fun a -> " " + this.ExportPriority a + " ")
    //    Unfolded it would be something like
    //       let printPriority (priority : Priority option) : String =
    //         match priority with
    //             | Some(priority) -> " " + (this.ExportPriority priority) + " "
    //             | None -> ""
    let printOptionalArgument (opt : 'a option) exporter : String =
        match opt with
            | Some(opt) -> exporter opt + " "
            | None -> ""
    
    member this.ExportUnarop (unarop : Unarop) : string =
        match unarop with
            | Unarop.Tilde -> "~"
            | Unarop.Neg   -> "-"
            | Unarop.Not   -> "!"

    member this.ExportAndor (andor : Andor) : string =
        match andor with
            | Andor.And  -> "&&"
            | Andor.Or   -> "||"
    
    member this.ExportBinarop (binarop : Binarop) : string =
        match binarop with
            | Add  -> "+"
            | Min  -> "-"
            | Mul  -> "*"
            | Div  -> "/"
            | Mod  -> "%"
            | BAnd -> "&"
            | Xor  -> "^"
            | BOr  -> "|"
            | Gt   -> ">"
            | Lt   -> "<"
            | Ge   -> ">="
            | Le   -> "<="
            | Eq   -> "=="
            | Neq  -> "!="
            | Bls  -> "<<"
            | Brs  -> ">>"
            | Andor andor -> this.ExportAndor andor // &&, ||
    
    member this.ExportConst (cons : Const) : string =
        match cons with
            | True  -> "true"
            | False -> "false"
            | Skip  -> "skip"
            | Number number -> number.ToString()

    // varref	: name [ '[' any_expr ']' ] [ '.' varref ]
    member this.ExportVarref (varref : Varref) : string =
        let printIndex (index : AnyExpr option) : String =
          match index with
              | Some(expr) -> "[" + (this.ExportAnyExpr expr) + "]"
              | None -> ""
        let printSubVarref (subvarref : Varref option) : String =
          match subvarref with
              | Some(varref) -> "." + (this.ExportVarref varref)
              | None -> ""
        match varref with
            | Varref.Varref (name,index,varref) -> name + (printIndex index) + (printSubVarref varref) // Varref.Varref of string * (AnyExpr option) * (Varref option)
        
    // any_expr: '(' any_expr ')' ...
    member this.ExportAnyExpr (anyexpr : AnyExpr) : string =
        match anyexpr with
            | BinaryExpr (left,op,right) -> "("+ (this.ExportAnyExpr left) + (this.ExportBinarop op) + (this.ExportAnyExpr right) + ")" // of AnyExpr * Binarop * AnyExpr
            | UnaryExpr (op,expr) -> "("+ (this.ExportUnarop op) + (this.ExportAnyExpr expr) + ")"  // of Unarop * AnyExpr
            | IfThenElse (guard,truebr,falsebr) -> "("+ (this.ExportAnyExpr guard) + "->" + (this.ExportAnyExpr truebr) + ":" + (this.ExportAnyExpr falsebr) + ")" // of AnyExpr * AnyExpr * AnyExpr
            | Varref varr -> this.ExportVarref varr // of Varref
            | Const cons -> this.ExportConst cons

    // expr	: any_expr ...
    member this.ExportExpr (expr : Expr) : string =
        match expr with
            | AnyExpr anyexpr -> this.ExportAnyExpr anyexpr // of AnyExpr
            | ExprAndOrExpr (left,op,right) -> "("+ (this.ExportExpr left) + (this.ExportAndor op) + (this.ExportExpr right) + ")" // of Expr * Andor * Expr

    member this.ExportVisible (modu : Visible) : string =
        match modu with
            | Hidden -> "hidden"
            | Show   -> "show"

    member this.ExportTypename (modu : Typename) : string =
        match modu with
            | Typename.Bit   -> "bit"
            | Typename.Bool  -> "bool"
            | Typename.Byte  -> "byte"
            | Typename.Short -> "short"
            | Typename.Int   -> "int"
            | Typename.Mtype -> "mype"
            | Typename.Chan  -> "chan"

    // ivar    : name [ '[' const ']' ] [ '=' any_expr | '=' ch_init ]
    member this.ExportIvar (ivar : Ivar) : string =
        let printSize (size : int32 option) : String =
          match size with
              | Some(size) -> "[" + size.ToString() + "]"
              | None -> ""
        let printSubAnyExpr (subanyexpr : AnyExpr option) : String =
          match subanyexpr with
              | Some(subanyexpr) -> " = " + (this.ExportAnyExpr subanyexpr)
              | None -> ""
        match ivar with
            | Ivar (name,size,expr) -> name + printSize size + printSubAnyExpr expr // of string * (int32 option) * (AnyExpr option)

    // one_decl: [ visible ] typename  ivar [',' ivar ] *
    member this.ExportOneDecl (onedecl : OneDecl) : string =
        let printVisible (visible : Visible option) : String =
          match visible with
              | Some(visible) -> this.ExportVisible visible + " "
              | None -> ""
        let printIvars (ivars : Ivar list) : String =
          ivars |> List.map this.ExportIvar
                |> List.reduce (fun acc r -> acc + ", " + r ) //after first element no ",". So we use reduce instead of fold. 1st element of list is initial accumulator
        match onedecl with
            | OneDecl (visible,typename,ivars) -> printVisible visible + this.ExportTypename typename + " " + printIvars ivars // of (Visible option) * Typename * (Ivar list)

    // decl_lst: one_decl [ ';' one_decl ] *
    member this.ExportDeclLst (lvl:int) (decllst : DeclLst) : string =
        let printOneDecls (onedecls : OneDecl list) : String =
          onedecls |> List.map this.ExportOneDecl
                   |> List.reduce (fun acc r -> acc + ";" + (nli lvl) + r ) //after first element no ";". So we use reduce instead of fold. 1st element of list is initial accumulator
        match decllst with
            | DeclLst decllst -> printOneDecls decllst // of (OneDecl list)

    // assign  : varref '=' any_expr	/* standard assignment */
    member this.ExportAssign (assign : Assign) : string =
        match assign with
            | AssignExpr (varref,expr) -> this.ExportVarref varref + " = " + this.ExportAnyExpr expr // of Varref * AnyExpr
            | Incr varref -> this.ExportVarref varref + "++" // of Varref
            | Decr varref -> this.ExportVarref varref + "--" // of Varref
    
    // range	: varref ':' expr '..' expr
    member this.ExportRange (lvl:int) (range : Range) : string =
        match range with
            | Range (varref, fromExpr, toExpr) -> this.ExportVarref varref + " : " + this.ExportExpr fromExpr + ".. " + this.ExportExpr toExpr //of Varref * Expr * Expr

    // step    : stmnt	[ UNLESS stmnt ]
    //          | decl_lst
    member this.ExportStep (lvl:int) (step : Step) : string =
        let printUnless (unlessStmnt : Stmnt option) : String =
          match unlessStmnt with
              | Some(unlessStmnt) -> " unless " + (this.ExportStmnt lvl) unlessStmnt
              | None -> ""        
        match step with
            | StmntStep (stmnt,unlessStmnt) -> (this.ExportStmnt lvl) stmnt + printUnless unlessStmnt // of Stmnt * (Stmnt option)
            | DeclListStep declliststep -> (this.ExportDeclLst lvl) declliststep // of DeclLst

    // sequence: step [ ';' step ] *
    member this.ExportSequence (lvl:int) (sequence : Sequence) : string =
        match sequence with
            | Sequence steps ->   // of Step list
                  steps |> List.map (this.ExportStep lvl)
                        |> List.reduce (fun acc r -> acc + ";" + (nli lvl) + r )  //after first element no ";". So we use reduce instead of fold. 1st element of list is initial accumulator
                        //|> (fun str -> str + (nli lvl)) //newline

    // options : ':' ':' sequence [ ':' ':' sequence ] *
    member this.ExportOptions (lvl:int) (oprions : Options) : string =
        let printOption (sequence : Sequence) : string =
            "::  " + (this.ExportSequence (lvl+2)) sequence //+ (nli lvl)
        match oprions with
            | Options oprions ->   // of Sequence list
                  oprions |> List.map printOption
                          |> List.reduce (fun acc r -> acc + (nli lvl) + r )

    // stmnt	: IF options FI		/* selection */
    member this.ExportStmnt (lvl:int) (stmnt : Stmnt) : string =
        match stmnt with
            | IfStmnt options      -> "if"+ (nli (lvl+1)) + (this.ExportOptions (lvl+1)) options + (nli lvl) + "fi" // of Options
            | DoStmnt options      -> "do" + (nli (lvl+1)) + (this.ExportOptions (lvl+1)) options + (nli lvl) + "od" // of Options
            | ForStmnt (range,seq) -> "for (" + (this.ExportRange lvl) range + " ) { " + (nli (lvl+1)) + (this.ExportSequence (lvl+1)) seq + (nli lvl) + "}" // of Range * Sequence
            | AtomicStmnt seq      -> "atomic {" + (nli (lvl+1)) + (this.ExportSequence (lvl+1)) seq + (nli lvl) + "}"  // of Sequence
            | DStepStmnt seq       -> "d_step {" + (nli (lvl+1)) + (this.ExportSequence (lvl+1)) seq + (nli lvl) + "}"  // of Sequence
            | SelectStmnt range    -> "select (" + (this.ExportRange lvl) range + " ) " // of Range
            | SequenceStmnt seq    -> "{ " + (nli (lvl+1)) + (this.ExportSequence (lvl+1)) seq + (nli lvl) + "}" // of Sequence
            | AssignStmnt assign   -> this.ExportAssign assign // of Assign
            | ElseStmnt            -> "else" // used inside options (if no other guard of the available options is true)
            | GotoStmnt label      -> "goto " + label // of string 
            | LabeledStmnt (lbl,st)-> "" + lbl + ": " + (this.ExportStmnt lvl) st // of string * Stmnt // as destination of goto
            | AssertStmnt expr     -> "assert " +  this.ExportExpr expr //of Expr
            | ExprStmnt expr       -> this.ExportExpr expr // of Expr

    member this.ExportPriority (priority : Priority) : string =
        match priority with
            | Int priority -> "priority " + priority.ToString() // of int32 //Standard is 1

    // init	: INIT [ priority ] '{' sequence '}'
    member this.ExportInit (lvl:int) (init : Init) : string =
        let printPriority (priority : Priority option) : String = printOptionalArgument priority (fun a -> " " + this.ExportPriority a + " ")
        match init with
            | Init (priority,seq) -> "init " + printPriority priority + (this.ExportSequence lvl) seq // of (Priority option) * Sequence

    // active  : ACTIVE [ '[' const ']' ]	/* instantiation */
    member this.ExportActive (active : Active) : string =
        let printConst (cons : Const option) : String = printOptionalArgument cons (fun a -> " [" + this.ExportConst a + "] ")
        match active with
            | Active cons -> "active" + printConst cons // of (Const option)

    // enabler : PROVIDED '(' expr ')'	/* execution constraint */
    member this.ExportEnabler (enabler : Enabler) : string =
        match enabler with
            | Expr expr -> "provided ( " + this.ExportExpr expr + " ) " // of Expr

    // proctype: [ active ] PROCTYPE name '(' [ decl_lst ]')'
    // 	         [ priority ] [ enabler ] '{' sequence '}'
    member this.ExportProctype (lvl:int) (proctype : Proctype) : string =
        let printActive (active : Active option) : String = printOptionalArgument active (fun a -> "" + (this.ExportActive) a + "")
        let printDeclLst (decllst : DeclLst option) : String = printOptionalArgument decllst (fun a -> " (" + (this.ExportDeclLst lvl) a + ") ")
        let printPriority (priority : Priority option) : String = printOptionalArgument priority (fun a -> "" + (this.ExportPriority) a + "")
        let printEnabler (enabler : Enabler option) : String = printOptionalArgument enabler (fun a -> "" + (this.ExportEnabler) a + "")
        match proctype with
            | Proctype (active,name,decls,priority,enabler,sequence) -> // of (Active option) * string * ( DeclLst option) * (Priority option) *  (Enabler option) * Sequence
                       printActive active +
                       "proctype " +
                       name +
                       "( " +
                       printDeclLst decls +
                       ") " +
                       printPriority priority +
                       printEnabler enabler +
                       "{" + (nli (lvl+1)) +
                       (this.ExportSequence (lvl+1)) sequence +
                       (nli lvl) +
                       "}" + (nli lvl)

    member this.ExportModule (lvl:int) (modu : Module) : string =
        match modu with
            | ProcTypeModule proc        -> (this.ExportProctype lvl) proc
            | InitModule init            -> (this.ExportInit lvl) init
            | GlobalVarsAndChans decllst -> (this.ExportDeclLst lvl) decllst
                    
    member this.ExporUnaryLtlOperator (unarop : UnaryLtlOperator) : string =
        match unarop with
            | UnaryLtlOperator.Always     -> "[]"
            | UnaryLtlOperator.Eventually -> "<>"
                
    member this.ExportBinaryLtlOperator (binarop : BinaryLtlOperator) : string =
        match binarop with
            | BinaryLtlOperator.Equals     -> "<->"
            | BinaryLtlOperator.Until      -> "U"
            | BinaryLtlOperator.WeakUntil  -> "W"
            | BinaryLtlOperator.Release    -> "V"
            | BinaryLtlOperator.And        -> "/\\"
            | BinaryLtlOperator.Or         -> "\\/"
            | BinaryLtlOperator.Implies    -> "->"
    
    member this.ExportLtlExpr (formula : LtlExpr) : string =
        match formula with
            | LtlExpr.BinaryExpr (left,op,right) -> "("+ (this.ExportLtlExpr left) + (this.ExportBinarop op) + (this.ExportLtlExpr right) + ")" // of AnyExpr * Binarop * AnyExpr
            | LtlExpr.UnaryExpr (op,expr) -> "("+ (this.ExportUnarop op) + (this.ExportLtlExpr expr) + ")"  // of Unarop * AnyExpr
            | LtlExpr.Varref varr -> this.ExportVarref varr // of Varref
            | LtlExpr.Const cons -> this.ExportConst cons
            | LtlExpr.BinaryLtlExpr (left,op,right) -> "("+ (this.ExportLtlExpr left) + (this.ExportBinaryLtlOperator op) + (this.ExportLtlExpr right) + ")" // of AnyExpr * Binarop * AnyExpr
            | LtlExpr.UnaryLtlExpr (expr,op) -> "("+ (this.ExporUnaryLtlOperator op) + (this.ExportLtlExpr expr) + ")"  // of Unarop * AnyExpr
            
    member this.ExportFormula (lvl:int) (formula: LtlExpr) : string =
        sprintf "ltl { %s } " (this.ExportLtlExpr formula)
    
    member this.ExportSpec (lvl:int) (spec : Spec) : string =
        let transformedCode =
            spec.Code |> List.map (this.ExportModule lvl)
                      |> List.reduce (fun acc r -> acc + ";"  + (nli lvl) + (nli lvl) + r ) //after first element no ";". So we use reduce instead of fold. 1st element of list is initial accumulator
                    //|> List.fold (fun acc r -> acc + r + (nli lvl) ) ""
        let transformedFormulas =
            spec.Formulas |> List.map (this.ExportFormula lvl)
                          |> String.concat "\n"

        sprintf "%s\n\n\n%s" transformedCode transformedFormulas

    member this.Export = this.ExportSpec 0


open SafetySharp.Workflow

type internal PromelaToString with
    static member instance : PromelaToString =
        PromelaToString()

    static member printWithLogEntriesWorkflow : SimpleWorkflowFunction<Spec,string,unit> = workflow {
        let! model = getState ()
        // TODO
        do! updateState (PromelaToString.instance.ExportSpec 0 model)
    }

    static member workflow : SimpleWorkflowFunction<Spec,string,unit> = workflow {
        let! model = getState ()
        do! updateState (PromelaToString.instance.ExportSpec 0 model)
    }