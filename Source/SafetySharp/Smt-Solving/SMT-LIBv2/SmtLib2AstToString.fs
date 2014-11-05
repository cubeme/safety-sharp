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

namespace SMTLIB2AstToFile

open SMTLIB2DataStructures.Ast
open System

exception NotImplementedYetException

type ExportSMTLIB2AstToFile() =

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
    
    // 3.1 Lexicon
    member this.ExportNumeral (numeral : SMTLIB2DataStructures.Ast.Numeral) : string =
        numeral.ToString()

    member this.ExportDecimal (decimal : SMTLIB2DataStructures.Ast.Decimal) : string =
        decimal

    member this.ExportHexadecimal (hex : SMTLIB2DataStructures.Ast.Hexadecimal) : string =
        hex

    member this.ExportBinary (bin : SMTLIB2DataStructures.Ast.Binary) : string =
        bin

    member this.ExportString (str : SMTLIB2DataStructures.Ast.String) : string =
        let a= "\"" + str + "\""
        // TODO: escape Characters
        let escaper (c:char) : string =
            match c with
                | '\b' -> "\\\b"
                | '\n' -> "\\n"
                | '\r' -> "\\r"
                | '\t' -> "\\t"
                | '\\' -> "\\\\"
                | '\"' -> "\\\""
                | '\'' -> "\\\'"
                //TODO: Unicode
                | _  -> c.ToString()
        str.ToCharArray() |> Array.toList
                          |> List.map escaper
                          |> List.fold (+) ""

    member this.ExportBValue (bvalue : bool) : string =
        match bvalue with
            | true -> "true"
            | false -> "false"

    member this.ExportReservedWords (resword : SMTLIB2DataStructures.Ast.ReservedWords) : string =
        match resword with 
            | ReservedWord_par             -> "par"
            | ReservedWord_NUMERAL         -> "NUMERAL"
            | ReservedWord_DECIMAL         -> "DECIMAL"
            | ReservedWord_STRING          -> "STRING"
            | ReservedWord_Underscore      -> "_"
            | ReservedWord_ExclamationMark -> "!"
            | ReservedWord_as              -> "as"
            | ReservedWord_let             -> "let"
            | ReservedWord_forall          -> "forall"
            | ReservedWord_exists          -> "exists"

    member this.ExportSymbol (symbol : SMTLIB2DataStructures.Ast.Symbol) : string =
        match symbol with
            | Symbol.Symbol str -> str

    member this.ExportKeyword (keyword : SMTLIB2DataStructures.Ast.Keyword) : string =
        match keyword with
            | Keyword.Keyword str -> ":" + str
    

    // 3.2 S-expressions
    member this.ExportSpecConstant (specconst : SMTLIB2DataStructures.Ast.SpecConstant) : string =
        match specconst with 
            | SpecConstantNumeral num     -> this.ExportNumeral num
            | SpecConstantDecimal dec     -> this.ExportDecimal dec
            | SpecConstantHexadecimal hex -> this.ExportHexadecimal hex
            | SpecConstantBinary bin      -> this.ExportBinary bin
            | SpecConstantString str      -> this.ExportString str

    member this.ExportSExpr (sexpr : SMTLIB2DataStructures.Ast.SExpr) : string =
        match sexpr with 
            | SExprSpecConstant specconst -> this.ExportSpecConstant specconst
            | SExprSymbol symbol          -> this.ExportSymbol symbol
            | SExprKeyword keyword        -> this.ExportKeyword keyword
            | SExprSExprList sexprs       -> "(" + (sexprs |> List.fold (fun acc sexpr -> acc + " " + this.ExportSExpr sexpr) "" ) + " )"


    // 3.3 Identifiers
    member this.ExportIdentifier (identifier : SMTLIB2DataStructures.Ast.Identifier) : string =
        match identifier with 
            | IdSymbol symbol             -> this.ExportSymbol symbol
            | IdIndexed (symbol, numlist) -> "( _ " + this.ExportSymbol symbol + "" + (numlist |> List.fold (fun acc numeral -> acc + " " + this.ExportNumeral numeral) "" ) + " )"
            

    // 3.4 Attributes
    member this.ExportAttributeValue (atrrvalue : SMTLIB2DataStructures.Ast.AttributeValue) : string =
        match atrrvalue with 
            | AttributeValueSpecConstant specconst -> this.ExportSpecConstant specconst
            | AttributeValueSymbol symbol          -> this.ExportSymbol symbol
            | AttributeValueSExprList sexprs       -> "(" + (sexprs |> List.fold (fun acc sexpr -> acc + " " + this.ExportSExpr sexpr) "" ) + " )"

    member this.ExportAttribute (attribute : SMTLIB2DataStructures.Ast.Attribute) : string =
        match attribute with 
            | AttributeKeyword keyword                      -> this.ExportKeyword keyword
            | AttributeKeywordWithValue (keyword,attrvalue) -> this.ExportKeyword keyword + " " + this.ExportAttributeValue attrvalue

    // 3.5 Sorts
    member this.ExportSort (sort : SMTLIB2DataStructures.Ast.Sort) : string =
        match sort with
            | SortSimple identifier -> this.ExportIdentifier identifier
            | SortAdvanced (identifier, sorts) -> "( " + this.ExportIdentifier identifier + "" + (sorts |> List.fold (fun acc sort -> acc + " " + this.ExportSort sort) "" ) + " )"


    // 3.6 Terms and Formulas
    member this.ExportQualIdentifier (qualid : SMTLIB2DataStructures.Ast.QualIdentifier) : string =
        match qualid with 
            | QualIdentifier identifier -> this.ExportIdentifier identifier
            | QualIdentifierOfSort (identifier, sort) -> "( as " + this.ExportIdentifier identifier + " " + this.ExportSort sort + " )"

    member this.ExportVarBinding ( (symbol, term) : SMTLIB2DataStructures.Ast.VarBinding) : string =
        "( " + this.ExportSymbol symbol + " " + this.ExportTerm term + " )"

    member this.ExportSortedVar ((symbol, sort) : SMTLIB2DataStructures.Ast.SortedVar) : string =
        "( " + this.ExportSymbol symbol + " " + this.ExportSort sort + " )"

    member this.ExportTerm (term : SMTLIB2DataStructures.Ast.Term) : string =
        let ExportTerms terms = (terms |> List.fold (fun acc term -> acc + " " + this.ExportTerm term) "" )
        let ExportVarbindings varbindings = (varbindings |> List.fold (fun acc varbinding -> acc + " " + this.ExportVarBinding varbinding ) "" )
        let ExportSortedVars sortedvars = (sortedvars |> List.fold (fun acc sortedvar -> acc + " " + this.ExportSortedVar sortedvar ) "" )
        let ExportAttributes attributes = (attributes |> List.fold (fun acc attribute -> acc + " " + this.ExportAttribute attribute ) "" )
        match term with
            | TermSpecConstant specconstant         -> this.ExportSpecConstant specconstant
            | TermQualIdentifier qualidentifier     -> this.ExportQualIdentifier qualidentifier
            | TermQualIdTerm (qualidentifier,terms) -> "( " + this.ExportQualIdentifier qualidentifier + "" + ExportTerms terms  + " )"
            | TermLetTerm (varbindings, term)       -> "( let "    + ExportVarbindings varbindings + "" + this.ExportTerm term + " )"
            | TermForAllTerm (sortedvars,term)      -> "( forall " + ExportSortedVars sortedvars   + "" + this.ExportTerm term + " )"
            | TermExistsTerm (sortedvars,term)      -> "( exists " + ExportSortedVars sortedvars   + "" + this.ExportTerm term + " )"
            | TermExclimationPt (term,attributes)   -> "( ! " + this.ExportTerm term + " " + ExportAttributes attributes + " )"


    // 3.7 Theory Declarations
    member this.ExportSortSymbolDecl (sortsymboldecl : SMTLIB2DataStructures.Ast.SortSymbolDecl) : string =
        raise NotImplementedYetException

    member this.ExportMetaSpecConstant (metaspecconstant : SMTLIB2DataStructures.Ast.MetaSpecConstant) : string =
        raise NotImplementedYetException

    member this.ExportFunSymbolDecl (funsymboldecl : SMTLIB2DataStructures.Ast.FunSymbolDecl) : string =
        raise NotImplementedYetException

    member this.ExportParFunSymbolDecl (parfunsymboldecl : SMTLIB2DataStructures.Ast.ParFunSymbolDecl) : string =
        raise NotImplementedYetException

    member this.ExportTheoryAttribute (theoryattribute : SMTLIB2DataStructures.Ast.TheoryAttribute) : string =
        raise NotImplementedYetException

    member this.ExportTheoryDecl (theorydecl : SMTLIB2DataStructures.Ast.TheoryDecl) : string =
        raise NotImplementedYetException
        

    // 3.8 Logic Declarations
    member this.ExportLogicAttribute (logicattribute : SMTLIB2DataStructures.Ast.LogicAttribute) : string =
        raise NotImplementedYetException
    member this.ExportLogic (logic : SMTLIB2DataStructures.Ast.Logic) : string =
        raise NotImplementedYetException

    // 3.9 Scripts, Part 1: Commands
    member this.ExportInfoFlag (infoflag : SMTLIB2DataStructures.Ast.InfoFlag) : string =
        match infoflag with
            | InfoFlagErrorBehavior   -> ":error-behavior"
            | InfoFlagName            -> ":name"
            | InfoFlagAuthors         -> ":authors"
            | InfoFlagVersion         -> ":version"
            | InfoFlagStatus          -> ":status"
            | InfoFlagReasonUnknown   -> ":reason-unknown"
            | InfoFlagKeyword keyword -> this.ExportKeyword keyword
            | InfoFlagAllStatistics   -> ":all-statistics"

    member this.ExportOption (option : SMTLIB2DataStructures.Ast.Option) : string =
        match option with
            | OptionPrintSuccess boolvalue       -> ":print-success"             + " " + this.ExportBValue boolvalue
            | OptionExpandDefinitions boolvalue  -> ":expand-definitions"        + " " + this.ExportBValue boolvalue
            | OptionInteractiveMode boolvalue    -> ":interactive-mode"          + " " + this.ExportBValue boolvalue
            | OptionProduceProofs boolvalue      -> ":produce-proofs"            + " " + this.ExportBValue boolvalue
            | OptionProduceUnsatCores boolvalue  -> ":produce-unsat-cores"       + " " + this.ExportBValue boolvalue
            | OptionProduceModels boolvalue      -> ":produce-models"            + " " + this.ExportBValue boolvalue
            | OptionProduceAssignments boolvalue -> ":produce-assignments"       + " " + this.ExportBValue boolvalue
            | OptionRegularOutputChannel str     -> ":regular-output-channel"    + " " + this.ExportString str
            | OptionDiagnosticOutputChannel str  -> ":diagnostic-output-channel" + " " + this.ExportString str
            | OptionRandomSeed numeral           -> ":random-seed"               + " " + this.ExportNumeral numeral
            | OptionVerbosity numeral            -> ":verbosity"                 + " " + this.ExportNumeral numeral
            | OptionAttribute attribute          -> this.ExportAttribute attribute

    member this.ExportCommand (command : SMTLIB2DataStructures.Ast.Command) : string =
        let ExportSymbols symbols = (symbols |> List.fold (fun acc symbol -> acc + " " + this.ExportSymbol symbol ) "" )
        let ExportSorts sorts  = (sorts |> List.fold (fun acc sort -> acc + " " + this.ExportSort sort) "" )
        let ExportSortedVars sortedvars = (sortedvars |> List.fold (fun acc sortedvar -> acc + " " + this.ExportSortedVar sortedvar ) "" )
        let ExportTerms terms = (terms |> List.fold (fun acc term -> acc + " " + this.ExportTerm term) "" )
        match command with
            | CommandSetLogic symbol                         -> "( "+ "set-logic"      + " " + this.ExportSymbol symbol + " )"
            | CommandSetOption option                        -> "( "+ "set-option"     + " " + this.ExportOption option + " )"
            | CommandSetInfo attribute                       -> "( "+ "set-info"       + " " + this.ExportAttribute attribute + " )"
            | CommandDeclareSort (symbol,numeral)            -> "( "+ "declare-sort"   + " " + this.ExportSymbol symbol + " " + this.ExportNumeral numeral + " )"
            | CommandDefineSort (symbol,symbols,sort)        -> "( "+ "define-sort"    + " " + this.ExportSymbol symbol + " " + "(" + ExportSymbols symbols       + " ) " + this.ExportSort sort + " )"
            | CommandDeclareFun(symbol,sorts,sort)           -> "( "+ "declare-fun"    + " " + this.ExportSymbol symbol + " " + "(" + ExportSorts sorts           + " ) " + this.ExportSort sort + " )"
            | CommandDefineFun (symbol,sortedvars,sort,term) -> "( "+ "define-fun"     + " " + this.ExportSymbol symbol + " " + "(" + ExportSortedVars sortedvars + " ) " + this.ExportSort sort + " " + this.ExportTerm term + " )"
            | CommandPush numeral                            -> "( "+ "push"           + " " + this.ExportNumeral numeral + " )"
            | CommandPop numeral                             -> "( "+ "pop"            + " " + this.ExportNumeral numeral + " )"
            | CommandAssert term                             -> "( "+ "assert"         + " " + this.ExportTerm term + " )"
            | CommandCheckSat                                -> "( "+ "check-sat"      + " )"
            | CommandGetAssertions                           -> "( "+ "get-assertions" + " )"
            | CommandGetProof                                -> "( "+ "get-proof"      + " )"
            | CommandGetUnsatCore                            -> "( "+ "get-unsat-core" + " )"
            | CommandGetValue terms                          -> "( "+ "get-value"      + " " + "(" + ExportTerms terms + " )" + " )"
            | CommandGetAssignment                           -> "( "+ "get-assignment" + " )"
            | CommandGetOption keyword                       -> "( "+ "get-option"     + " " + this.ExportKeyword keyword + " )"
            | CommandGetInfo infoflag                        -> "( "+ "get-info"       + " " + this.ExportInfoFlag infoflag + " )"
            | CommandExit                                    -> "( "+ "exit"           + " )"

    member this.ExportScript (script : SMTLIB2DataStructures.Ast.Script) : string =
        script |> List.fold (fun acc command -> this.ExportCommand command + nl ) ""


    member this.Export = this.ExportScript