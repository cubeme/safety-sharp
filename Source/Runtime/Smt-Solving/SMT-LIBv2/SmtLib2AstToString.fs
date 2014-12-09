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

namespace SafetySharp.Internal.SmtSolving.SmtLib2.AstToString

open SafetySharp.Internal.SmtSolving.SmtLib2.SmtShortTypes
open System

exception NotImplementedYetException

type internal ExportSMTLIB2AstToFile() =

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
    member this.ExportNumeral (numeral : Smt2Numeral) : string =
        numeral.ToString()

    member this.ExportDecimal (decimal : Smt2Decimal) : string =
        decimal

    member this.ExportHexadecimal (hex : Smt2Hexadecimal) : string =
        hex

    member this.ExportBinary (bin : Smt2Binary) : string =
        bin

    member this.ExportString (str : Smt2String) : string =
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

    member this.ExportReservedWords (resword : Smt2ReservedWords) : string =
        match resword with 
            | Smt2ReservedWords.ReservedWord_par             -> "par"
            | Smt2ReservedWords.ReservedWord_NUMERAL         -> "NUMERAL"
            | Smt2ReservedWords.ReservedWord_DECIMAL         -> "DECIMAL"
            | Smt2ReservedWords.ReservedWord_STRING          -> "STRING"
            | Smt2ReservedWords.ReservedWord_Underscore      -> "_"
            | Smt2ReservedWords.ReservedWord_ExclamationMark -> "!"
            | Smt2ReservedWords.ReservedWord_as              -> "as"
            | Smt2ReservedWords.ReservedWord_let             -> "let"
            | Smt2ReservedWords.ReservedWord_forall          -> "forall"
            | Smt2ReservedWords.ReservedWord_exists          -> "exists"

    member this.ExportSymbol (symbol : Smt2Symbol) : string =
        match symbol with
            | Smt2Symbol.Symbol str -> str

    member this.ExportKeyword (keyword : Smt2Keyword) : string =
        match keyword with
            | Smt2Keyword.Keyword str -> ":" + str
    

    // 3.2 S-expressions
    member this.ExportSpecConstant (specconst : Smt2SpecConstant) : string =
        match specconst with 
            | Smt2SpecConstant.SpecConstantNumeral num     -> this.ExportNumeral num
            | Smt2SpecConstant.SpecConstantDecimal dec     -> this.ExportDecimal dec
            | Smt2SpecConstant.SpecConstantHexadecimal hex -> this.ExportHexadecimal hex
            | Smt2SpecConstant.SpecConstantBinary bin      -> this.ExportBinary bin
            | Smt2SpecConstant.SpecConstantString str      -> this.ExportString str

    member this.ExportSExpr (sexpr : Smt2SExpr) : string =
        match sexpr with 
            | Smt2SExpr.SExprSpecConstant specconst -> this.ExportSpecConstant specconst
            | Smt2SExpr.SExprSymbol symbol          -> this.ExportSymbol symbol
            | Smt2SExpr.SExprKeyword keyword        -> this.ExportKeyword keyword
            | Smt2SExpr.SExprSExprList sexprs       -> "(" + (sexprs |> List.fold (fun acc sexpr -> acc + " " + this.ExportSExpr sexpr) "" ) + " )"


    // 3.3 Identifiers
    member this.ExportIdentifier (identifier : Smt2Identifier) : string =
        match identifier with 
            | Smt2Identifier.IdSymbol symbol             -> this.ExportSymbol symbol
            | Smt2Identifier.IdIndexed (symbol, numlist) -> "( _ " + this.ExportSymbol symbol + "" + (numlist |> List.fold (fun acc numeral -> acc + " " + this.ExportNumeral numeral) "" ) + " )"
            

    // 3.4 Attributes
    member this.ExportAttributeValue (atrrvalue : Smt2AttributeValue) : string =
        match atrrvalue with 
            | Smt2AttributeValue.AttributeValueSpecConstant specconst -> this.ExportSpecConstant specconst
            | Smt2AttributeValue.AttributeValueSymbol symbol          -> this.ExportSymbol symbol
            | Smt2AttributeValue.AttributeValueSExprList sexprs       -> "(" + (sexprs |> List.fold (fun acc sexpr -> acc + " " + this.ExportSExpr sexpr) "" ) + " )"

    member this.ExportAttribute (attribute : Smt2Attribute) : string =
        match attribute with 
            | Smt2Attribute.AttributeKeyword keyword                      -> this.ExportKeyword keyword
            | Smt2Attribute.AttributeKeywordWithValue (keyword,attrvalue) -> this.ExportKeyword keyword + " " + this.ExportAttributeValue attrvalue

    // 3.5 Sorts
    member this.ExportSort (sort : Smt2Sort) : string =
        match sort with
            | Smt2Sort.SortSimple identifier -> this.ExportIdentifier identifier
            | Smt2Sort.SortAdvanced (identifier, sorts) -> "( " + this.ExportIdentifier identifier + "" + (sorts |> List.fold (fun acc sort -> acc + " " + this.ExportSort sort) "" ) + " )"


    // 3.6 Terms and Formulas
    member this.ExportQualIdentifier (qualid : Smt2QualIdentifier) : string =
        match qualid with 
            | Smt2QualIdentifier.QualIdentifier identifier -> this.ExportIdentifier identifier
            | Smt2QualIdentifier.QualIdentifierOfSort (identifier, sort) -> "( as " + this.ExportIdentifier identifier + " " + this.ExportSort sort + " )"

    member this.ExportVarBinding ( (symbol, term) : Smt2VarBinding) : string =
        "( " + this.ExportSymbol symbol + " " + this.ExportTerm term + " )"

    member this.ExportSortedVar ((symbol, sort) : Smt2SortedVar) : string =
        "( " + this.ExportSymbol symbol + " " + this.ExportSort sort + " )"

    member this.ExportTerm (term : Smt2Term) : string =
        let ExportTerms terms = (terms |> List.fold (fun acc term -> acc + " " + this.ExportTerm term) "" )
        let ExportVarbindings varbindings = (varbindings |> List.fold (fun acc varbinding -> acc + " " + this.ExportVarBinding varbinding ) "" )
        let ExportSortedVars sortedvars = (sortedvars |> List.fold (fun acc sortedvar -> acc + " " + this.ExportSortedVar sortedvar ) "" )
        let ExportAttributes attributes = (attributes |> List.fold (fun acc attribute -> acc + " " + this.ExportAttribute attribute ) "" )
        match term with
            | Smt2Term.TermSpecConstant specconstant         -> this.ExportSpecConstant specconstant
            | Smt2Term.TermQualIdentifier qualidentifier     -> this.ExportQualIdentifier qualidentifier
            | Smt2Term.TermQualIdTerm (qualidentifier,terms) -> "( " + this.ExportQualIdentifier qualidentifier + "" + ExportTerms terms  + " )"
            | Smt2Term.TermLetTerm (varbindings, term)       -> "( let "    + ExportVarbindings varbindings + "" + this.ExportTerm term + " )"
            | Smt2Term.TermForAllTerm (sortedvars,term)      -> "( forall " + ExportSortedVars sortedvars   + "" + this.ExportTerm term + " )"
            | Smt2Term.TermExistsTerm (sortedvars,term)      -> "( exists " + ExportSortedVars sortedvars   + "" + this.ExportTerm term + " )"
            | Smt2Term.TermExclimationPt (term,attributes)   -> "( ! " + this.ExportTerm term + " " + ExportAttributes attributes + " )"


    // 3.7 Theory Declarations
    member this.ExportSortSymbolDecl (sortsymboldecl : Smt2SortSymbolDecl) : string =
        raise NotImplementedYetException

    member this.ExportMetaSpecConstant (metaspecconstant : Smt2MetaSpecConstant) : string =
        raise NotImplementedYetException

    member this.ExportFunSymbolDecl (funsymboldecl : Smt2FunSymbolDecl) : string =
        raise NotImplementedYetException

    member this.ExportParFunSymbolDecl (parfunsymboldecl : Smt2ParFunSymbolDecl) : string =
        raise NotImplementedYetException

    member this.ExportTheoryAttribute (theoryattribute : Smt2TheoryAttribute) : string =
        raise NotImplementedYetException

    member this.ExportTheoryDecl (theorydecl : Smt2TheoryDecl) : string =
        raise NotImplementedYetException
        

    // 3.8 Logic Declarations
    member this.ExportLogicAttribute (logicattribute : Smt2LogicAttribute) : string =
        raise NotImplementedYetException
    member this.ExportLogic (logic : Smt2Logic) : string =
        raise NotImplementedYetException

    // 3.9 Scripts, Part 1: Commands
    member this.ExportInfoFlag (infoflag : Smt2InfoFlag) : string =
        match infoflag with
            | Smt2InfoFlag.InfoFlagErrorBehavior   -> ":error-behavior"
            | Smt2InfoFlag.InfoFlagName            -> ":name"
            | Smt2InfoFlag.InfoFlagAuthors         -> ":authors"
            | Smt2InfoFlag.InfoFlagVersion         -> ":version"
            | Smt2InfoFlag.InfoFlagStatus          -> ":status"
            | Smt2InfoFlag.InfoFlagReasonUnknown   -> ":reason-unknown"
            | Smt2InfoFlag.InfoFlagKeyword keyword -> this.ExportKeyword keyword
            | Smt2InfoFlag.InfoFlagAllStatistics   -> ":all-statistics"

    member this.ExportOption (option : Smt2Option) : string =
        match option with
            | Smt2Option.OptionPrintSuccess boolvalue       -> ":print-success"             + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionExpandDefinitions boolvalue  -> ":expand-definitions"        + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionInteractiveMode boolvalue    -> ":interactive-mode"          + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionProduceProofs boolvalue      -> ":produce-proofs"            + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionProduceUnsatCores boolvalue  -> ":produce-unsat-cores"       + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionProduceModels boolvalue      -> ":produce-models"            + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionProduceAssignments boolvalue -> ":produce-assignments"       + " " + this.ExportBValue boolvalue
            | Smt2Option.OptionRegularOutputChannel str     -> ":regular-output-channel"    + " " + this.ExportString str
            | Smt2Option.OptionDiagnosticOutputChannel str  -> ":diagnostic-output-channel" + " " + this.ExportString str
            | Smt2Option.OptionRandomSeed numeral           -> ":random-seed"               + " " + this.ExportNumeral numeral
            | Smt2Option.OptionVerbosity numeral            -> ":verbosity"                 + " " + this.ExportNumeral numeral
            | Smt2Option.OptionAttribute attribute          -> this.ExportAttribute attribute

    member this.ExportCommand (command : Smt2Command) : string =
        let ExportSymbols symbols = (symbols |> List.fold (fun acc symbol -> acc + " " + this.ExportSymbol symbol ) "" )
        let ExportSorts sorts  = (sorts |> List.fold (fun acc sort -> acc + " " + this.ExportSort sort) "" )
        let ExportSortedVars sortedvars = (sortedvars |> List.fold (fun acc sortedvar -> acc + " " + this.ExportSortedVar sortedvar ) "" )
        let ExportTerms terms = (terms |> List.fold (fun acc term -> acc + " " + this.ExportTerm term) "" )
        match command with
            | Smt2Command.CommandSetLogic symbol                         -> "( "+ "set-logic"      + " " + this.ExportSymbol symbol + " )"
            | Smt2Command.CommandSetOption option                        -> "( "+ "set-option"     + " " + this.ExportOption option + " )"
            | Smt2Command.CommandSetInfo attribute                       -> "( "+ "set-info"       + " " + this.ExportAttribute attribute + " )"
            | Smt2Command.CommandDeclareSort (symbol,numeral)            -> "( "+ "declare-sort"   + " " + this.ExportSymbol symbol + " " + this.ExportNumeral numeral + " )"
            | Smt2Command.CommandDefineSort (symbol,symbols,sort)        -> "( "+ "define-sort"    + " " + this.ExportSymbol symbol + " " + "(" + ExportSymbols symbols       + " ) " + this.ExportSort sort + " )"
            | Smt2Command.CommandDeclareFun(symbol,sorts,sort)           -> "( "+ "declare-fun"    + " " + this.ExportSymbol symbol + " " + "(" + ExportSorts sorts           + " ) " + this.ExportSort sort + " )"
            | Smt2Command.CommandDefineFun (symbol,sortedvars,sort,term) -> "( "+ "define-fun"     + " " + this.ExportSymbol symbol + " " + "(" + ExportSortedVars sortedvars + " ) " + this.ExportSort sort + " " + this.ExportTerm term + " )"
            | Smt2Command.CommandPush numeral                            -> "( "+ "push"           + " " + this.ExportNumeral numeral + " )"
            | Smt2Command.CommandPop numeral                             -> "( "+ "pop"            + " " + this.ExportNumeral numeral + " )"
            | Smt2Command.CommandAssert term                             -> "( "+ "assert"         + " " + this.ExportTerm term + " )"
            | Smt2Command.CommandCheckSat                                -> "( "+ "check-sat"      + " )"
            | Smt2Command.CommandGetAssertions                           -> "( "+ "get-assertions" + " )"
            | Smt2Command.CommandGetProof                                -> "( "+ "get-proof"      + " )"
            | Smt2Command.CommandGetUnsatCore                            -> "( "+ "get-unsat-core" + " )"
            | Smt2Command.CommandGetValue terms                          -> "( "+ "get-value"      + " " + "(" + ExportTerms terms + " )" + " )"
            | Smt2Command.CommandGetAssignment                           -> "( "+ "get-assignment" + " )"
            | Smt2Command.CommandGetOption keyword                       -> "( "+ "get-option"     + " " + this.ExportKeyword keyword + " )"
            | Smt2Command.CommandGetInfo infoflag                        -> "( "+ "get-info"       + " " + this.ExportInfoFlag infoflag + " )"
            | Smt2Command.CommandExit                                    -> "( "+ "exit"           + " )"

    member this.ExportScript (script : Smt2Script) : string =
        script |> List.fold (fun acc command -> this.ExportCommand command + nl ) ""


    member this.Export = this.ExportScript