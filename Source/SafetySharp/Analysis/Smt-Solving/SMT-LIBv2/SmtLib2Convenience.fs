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

namespace SafetySharp.Internal.SmtSolving.SmtLib2

module internal SmtShortTypes =
    open SafetySharp.Internal.SmtSolving.SmtLib2.Ast

    type Smt2Numeral = Numeral
    type Smt2Decimal = Decimal
    type Smt2Hexadecimal = Hexadecimal
    type Smt2Binary = Binary
    type Smt2String = String
    type Smt2ReservedWords = ReservedWords
    type Smt2Symbol = Symbol
    type Smt2Keyword = Keyword            
    type Smt2SpecConstant = SpecConstant
    type Smt2SExpr = SExpr
    type Smt2Identifier = Identifier
    type Smt2AttributeValue = AttributeValue
    type Smt2Attribute = Attribute
    type Smt2Sort = Sort
    type Smt2QualIdentifier = QualIdentifier
    type Smt2VarBinding = VarBinding
    type Smt2SortedVar = SortedVar
    type Smt2Term = Term
    type Smt2SortSymbolDecl = SortSymbolDecl
    type Smt2MetaSpecConstant = MetaSpecConstant
    type Smt2FunSymbolDecl = FunSymbolDecl
    type Smt2ParFunSymbolDecl = ParFunSymbolDecl
    type Smt2TheoryAttribute = TheoryAttribute
    type Smt2TheoryDecl = TheoryDecl
    type Smt2LogicAttribute = LogicAttribute
    type Smt2Logic = Logic
    type Smt2InfoFlag = InfoFlag
    type Smt2Option = Option
    type Smt2ICommand = ICommand
    type Smt2Command = Command
    type Smt2Script = Script
    type Smt2GenResponse = GenResponse
    type Smt2ErrorBehavior = ErrorBehavior
    type Smt2ReasonUnknown = ReasonUnknown
    type Smt2Status = Status
    type Smt2InfoResponse = InfoResponse
    type Smt2GetInfoResponse = GetInfoResponse
    type Smt2CheckSatResponse = CheckSatResponse
    type Smt2GetAssertionsResponse = GetAssertionsResponse
    type Smt2Proof = Proof
    type Smt2GetProofResponse = GetProofResponse
    type Smt2GetUnsatCoreResponse = GetUnsatCoreResponse
    type Smt2ValuationPair = ValuationPair
    type Smt2GetValueResponse = GetValueResponse
    type Smt2TValuationPair = TValuationPair
    type Smt2GetAssignmentResponse = GetAssignmentResponse
    type Smt2GetOptionResponse = GetOptionResponse


module internal SMTLIB2Convenience =

    open SafetySharp.Internal.SmtSolving.SmtLib2.Ast

    let IdentifierFromString str = 
        Identifier.IdSymbol(Symbol.Symbol(str))

    let SortFromString str =
        Sort.SortSimple(IdentifierFromString str)

    let QualifiedIdentifierFromString str=
        QualIdentifier.QualIdentifier(IdentifierFromString str)