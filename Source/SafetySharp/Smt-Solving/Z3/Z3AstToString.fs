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

namespace Z3AstToFile

open Z3DataStructures.Ast
open SMTLIB2DataStructures.Ast
open System

exception NotImplementedYetException
exception UnsupportedICommand

type ExportZ3AstToFile() =
    let smt2exporter = SMTLIB2AstToFile.ExportSMTLIB2AstToFile()

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
    
    
    
    member this.ExportTactics (tactics : Tactics) : string =
        match tactics with
            | TacticsSkip              -> "skip"
            | TacticsSolveEqs          -> "solve-eqs"
            | TacticsSplitClause       -> "split-clause"
            | TacticsSimplify          -> "simplify"
            | TacticsCtxSolverSimplify -> "ctx-solver-simplify"
            | TacticsAig               -> "aig" // tries to compress Boolean formulas using And-Inverted Graphs
            | TacticsNormalizeBounds   -> "normalize-bounds"

    member this.ExportParameter (parameter : Parameter) : string =
        raise NotImplementedYetException
    
    member this.ExportTacticals (tacticals : Tacticals) : string =
        let ExportTacticalss tacticalss = tacticalss |> List.fold (fun acc tacticals -> acc + " " + this.ExportTacticals tacticals ) ""
        let ExportParameters parameters = parameters |> List.fold (fun acc parameter -> acc + " " + this.ExportParameter parameter ) ""
        match tacticals with
            | TacticalsTactics tactics                            -> this.ExportTactics tactics
            | TacticalsThen tacticals                             -> "( " + "then"         + ExportTacticalss tacticals + " )"
            | TacticalsParThen tacticals                          -> "( " + "par-then"     + ExportTacticalss tacticals + " )"
            | TacticalsOrElse tacticals                           -> "( " + "or-else"      + ExportTacticalss tacticals + " )"
            | TacticalsIfThenElse (cond,thenBranch,elseBranch)    -> "( " + "if"           + " " + this.ExportTacticals cond + " " + this.ExportTacticals thenBranch + " " + this.ExportTacticals thenBranch + " )"
            | TacticalsWhen (cond,thenBranch)                     -> "( " + "when"         + " " + this.ExportTacticals cond + " " + this.ExportTacticals thenBranch + " )"
            | TacticalsParOr tacticals                            -> "( " + "par-or"       + ExportTacticalss tacticals + " )"
            | TacticalsRepeat tactical                            -> "( " + "repeat"       + " " + this.ExportTacticals tactical + " )"
            | TacticalsRepeatUntilN (tactical, maxIterations:int) -> "( " + "repeat"       + " " + this.ExportTacticals tactical + " " + maxIterations.ToString() + " )"
            | TacticalsTryForTime (tactical, maxTimeInMs:int)     -> "( " + "try-for"      + " " + this.ExportTacticals tactical + " " + maxTimeInMs.ToString() + " )"
            | TacticalsUsingParameter (tactical,parameters)       -> raise NotImplementedYetException // "( " + "using-params" + " " + this.ExportTacticals tactical + " " + ExportParameters parameters + " )"
    
     (*
     (declare-datatypes (<symbol>* ) (<datatype-declaration>+))
        declare mutually recursive datatypes.
        <datatype-declaration> ::= (<symbol> <constructor-decl>+)
        <constructor-decl> ::= (<symbol> <accessor-decl>* )
        <accessor-decl> ::= (<symbol> <sort>)
        example: (declare-datatypes (T) ((BinTree (leaf (value T)) (node (left BinTree) (right BinTree)))))
    *)
    member this.ExportDeclareDatatypes (datatypes:DeclareDataTypes) : string =
        let ExportAccessorDecl (con:AccessorDecl) =
            "( " + smt2exporter.ExportSymbol con.accessPartialContentFunctionName + " " + smt2exporter.ExportSort con.typeOfPartialContent + " )"
        let ExportConstructorDecl (cons:ConstructorDecl)=
            let ExportAccessorDecls = cons.content |> List.fold (fun (acc:string) con -> acc + " " + (ExportAccessorDecl con)) ""
            "( " + (smt2exporter.ExportSymbol cons.constructorName) + " " + ExportAccessorDecls + " )"
        let ExportDataTypeDecl (dt:DatatypeDeclaration) : string =
            let ExportConstructorDecl = dt.constructors |> List.fold (fun (acc:string) cons -> acc + " " + (ExportConstructorDecl cons)) ""
            "( " + smt2exporter.ExportSymbol dt.nameOfDatatype + " " + ExportConstructorDecl + " )"
        let ExportDatatypes =
            let ExportDataTypeDecls =
                datatypes.datatypes |> List.fold (fun (acc:string) dt -> acc + " " + (ExportDataTypeDecl dt)) ""
            "( " + ExportDataTypeDecls + " )"
        let ExportFormalParameters =
            "( " + (datatypes.formalParameters |> List.fold (fun acc sym -> acc + " " + smt2exporter.ExportSymbol sym) "" ) + " )"
        "( " + "declare-datatypes" + " " + ExportFormalParameters + " " + ExportDatatypes + " )"
        
    // To get more information, use "(help)" in the Z3-Shell
    member this.ExportCommandZ3 (command:CommandZ3) : string =
        let ExportParameters parameters = parameters |> List.fold (fun acc parameter -> acc + " " + this.ExportParameter parameter ) ""
        match command with
            | CommandZ3Apply (tactical,parameters)         -> "( " + "apply"     + " " + this.ExportTacticals tactical + " " + ExportParameters parameters + " )"
            | CommandZ3CheckSatUsing (tactical,parameters) -> raise NotImplementedYetException
            | CommandZ3GetModel                            -> "( " + "get-model" + " )"
            | CommandZ3DeclareConst (symbol,sort)          -> "( " + "declare-const" + " " + smt2exporter.ExportSymbol symbol + " " + smt2exporter.ExportSort sort + " )"
            | CommandZ3DeclareDatatypes datatypes          -> this.ExportDeclareDatatypes datatypes
            | CommandZ3Reset                               -> "( " + "reset"     + " )"
            | CommandZ3Simplify                            -> "( " + "simplify"  + " )"
    
    member this.ExportCommands (commands:ICommand list) : string =
        let ExportICommand (command:ICommand) : string =
            match command with
                | :? Command   as command -> smt2exporter.ExportCommand command
                | :? CommandZ3 as command -> this.ExportCommandZ3 command
                | _ -> raise UnsupportedICommand
        commands |> List.map ExportICommand
                 |> List.fold (fun acc cmd -> acc + "\n" + cmd) ""

    member this.Export = this.ExportCommands