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

namespace SMTLIB2DataStructures.Ast

// inspired by 
// http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf
// http://www.cs.uiowa.edu/~astump/software/ocaml-smt2.zip
// http://www.grammatech.com/resources/smt/SMTLIBTutorial.pdf

// 3.1 Lexicon             -> Common for Input and Output of SMT-Solver
// 3.2 S-expressions       -> Common for Input and Output of SMT-Solver
// 3.3 Identifiers         -> Common for Input and Output of SMT-Solver
// 3.4 Attributes          -> Common for Input and Output of SMT-Solver
// 3.5 Sorts               -> Common for Input and Output of SMT-Solver
// 3.6 Terms and Formulas  -> Common for Input and Output of SMT-Solver
// 3.7 Theory Declarations -> Input of SMT-Solver only 
// 3.8 Logic Declarations  -> Input of SMT-Solver only
// 3.9 Scripts Part 0      -> Common for Input and Output of SMT-Solver
// 3.9 Scripts Part 1:     -> Input of SMT-Solver only
//     Commands
// 3.9 Scripts Part 2:     -> Output of SMT-Solver only
//     Command Responses

// 3.1 Lexicon

type Numeral = bigint

type Decimal = string

type Hexadecimal = string

type Binary = string

type String = string

type ReservedWords = ReservedWord_par
                   | ReservedWord_NUMERAL 
                   | ReservedWord_DECIMAL 
                   | ReservedWord_STRING
                   | ReservedWord_Underscore
                   | ReservedWord_ExclamationMark
                   | ReservedWord_as
                   | ReservedWord_let
                   | ReservedWord_forall
                   | ReservedWord_exists

type Symbol = Symbol of string //= SimpleSymbol | QuotedSymbol

type Keyword = Keyword of string
            
// 3.2 S-expressions
(*
*)
type SpecConstant = SpecConstantNumeral of Numeral
                  | SpecConstantDecimal of Decimal
                  | SpecConstantHexadecimal of Hexadecimal
                  | SpecConstantBinary of Binary
                  | SpecConstantString of String

type SExpr = SExprSpecConstant of SpecConstant
           | SExprSymbol of Symbol
           | SExprKeyword of Keyword
           | SExprSExprList of SExpr list

// 3.3 Identifiers

type Identifier = IdSymbol of Symbol
                | IdIndexed of Symbol * Numeral list

// 3.4 Attributes

type AttributeValue = AttributeValueSpecConstant of SpecConstant
                    | AttributeValueSymbol of Symbol
                    | AttributeValueSExprList of SExpr list

type Attribute = AttributeKeyword of Keyword
               | AttributeKeywordWithValue of Keyword * AttributeValue

// 3.5 Sorts

//TODO: find better names
type Sort = SortSimple of Identifier
          | SortAdvanced of Identifier * Sort list

// 3.6 Terms and Formulas

type QualIdentifier = QualIdentifier of Identifier
                    | QualIdentifierOfSort of Identifier * Sort

and VarBinding = Symbol * Term

and SortedVar = Symbol * Sort

and Term = TermSpecConstant of SpecConstant
         | TermQualIdentifier of QualIdentifier
         | TermQualIdTerm of QualIdentifier * Term list
         | TermLetTerm of VarBinding list * Term
         | TermForAllTerm of (SortedVar list) * Term
         | TermExistsTerm of (SortedVar list) * Term
         | TermExclimationPt of Term * Attribute list

// 3.7 Theory Declarations

type SortSymbolDecl = Identifier * Numeral  * Attribute list

type MetaSpecConstant = Numeral
                      | Decimal
                      | String

type FunSymbolDecl = FunSymbolDecl1 of SpecConstant * Sort * Attribute list
                   | FunSymbolDecl2 of MetaSpecConstant * Sort * Attribute list
                   | FunSymbolDecl3 of Identifier * Sort list * Attribute list

type ParFunSymbolDecl = ParFunSymbolDecl1 of FunSymbolDecl
                      | ParFunSymbolDecl2 of Symbol list
                      | ParFunSymbolDecl3 of Identifier * Sort list * Attribute list

type TheoryAttribute = TheoryAttributeSorts of SortSymbolDecl list // syntax description: SortSymbol instead of SortSymbolDecl
                     | TheoryAttributeFuns of ParFunSymbolDecl list
                     | TheoryAttributeSortsDescription of string
                     | TheoryAttributeFunsDescription of string
                     | TheoryAttributeDefinition of string
                     | TheoryAttributeValues of string
                     | TheoryAttributeNotes of string
                     | TheoryAttributeAttribute of Attribute

type TheoryDecl = Symbol * TheoryAttribute list

// 3.8 Logic Declarations

type LogicAttribute = LogicAttributeTheories of Symbol list
                    | LogicAttributeLanguage of string
                    | LogicAttributeExtensions of string
                    | LogicAttributeValues of string
                    | LogicAttributeNotes of string
                    | LogicAttributeAttribute of Attribute

type Logic = Symbol * LogicAttribute list

// 3.9 Scripts, Part 1: Commands

type InfoFlag = InfoFlagErrorBehavior
              | InfoFlagName
              | InfoFlagAuthors
              | InfoFlagVersion
              | InfoFlagStatus
              | InfoFlagReasonUnknown
              | InfoFlagKeyword of Keyword
              | InfoFlagAllStatistics

type Option = OptionPrintSuccess of bool
            | OptionExpandDefinitions of bool
            | OptionInteractiveMode of bool
            | OptionProduceProofs of bool
            | OptionProduceUnsatCores of bool
            | OptionProduceModels of bool
            | OptionProduceAssignments of bool
            | OptionRegularOutputChannel of string
            | OptionDiagnosticOutputChannel of string
            | OptionRandomSeed of Numeral
            | OptionVerbosity of Numeral
            | OptionAttribute of Attribute

type ICommand = interface end

type Command = CommandSetLogic of Symbol
             | CommandSetOption of Option
             | CommandSetInfo of Attribute
             | CommandDeclareSort of name:Symbol * numberOfParameters:Numeral
             | CommandDefineSort of name:Symbol * formalParameters:Symbol list * definitionIsAbbreviationFor:Sort     // Serves more ore less as macro. Note: The Tutorial describes a more elaborated version of this term (p. 36). Here we use the simpler form of the standard of SMTLIB v2.0-r12.09.09
             | CommandDeclareFun of name:Symbol * formalParameters:Sort list * returnSort:Sort
             | CommandDefineFun of name:Symbol * formalParameters:SortedVar list * returnSort:Sort * definitionIsAbbreviationFor:Term // Serves more ore less as macro
             | CommandPush of Numeral
             | CommandPop of Numeral
             | CommandAssert of Term
             | CommandCheckSat
             | CommandGetAssertions
             | CommandGetProof
             | CommandGetUnsatCore
             | CommandGetValue of Term list
             | CommandGetAssignment
             | CommandGetOption of Keyword
             | CommandGetInfo of InfoFlag
             | CommandExit
             with interface ICommand

type Script = Command list

// 3.9 Scripts, Part 2: Command Responses

type GenResponse = GenResponseUnsupported
                 | GenResponseSuccess
                 | GenResponseError of string

type ErrorBehavior = ImmediateExit
                   | ContinuedExecution

type ReasonUnknown = ReasonUnknownMemout
                   | ReasonUnknownIncomplete

type Status = StatusSat
            | StatusUnsat
            | StatusUnknown

type InfoResponse = InfoResponseErrorBehavior of ErrorBehavior
                  | InfoResponseName of string
                  | InfoResponseAuthors of string
                  | InfoResponseVersion of string
                  | InfoResponseReasonUnknown of ReasonUnknown
                  | InfoResponseAttribute of Attribute

// response of Command.CommandGetInfo
type GetInfoResponse = InfoResponse list

// response of Command.CommandCheckSat
type CheckSatResponse = Status

// response of Command.CommandGetAssertions
type GetAssertionsResponse = Term list

type Proof = SExpr

// response of Command.CommandGetProof
type GetProofResponse = Proof

// response of Command.CommandGetUnsatCore
type GetUnsatCoreResponse = Symbol list

type ValuationPair = Term * Term

// response of Command.CommandGetValue
type GetValueResponse = ValuationPair list

type TValuationPair = Symbol * bool

// response of Command.CommandGetAssignment
type GetAssignmentResponse = TValuationPair list

// response of Command.CommandGetOption
type GetOptionResponse = AttributeValue
