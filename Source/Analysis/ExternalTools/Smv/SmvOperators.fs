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

namespace SafetySharp.ExternalTools.Smv

type internal UnaryOperator = 
    | LogicalNot

type internal BinaryOperator=      
    | LogicalAnd
    | LogicalOr
    | LogicalXor
    | LogicalNxor
    | LogicalImplies
    | LogicalEquivalence
    | Equality
    | Inequality
    | LessThan
    | GreaterThan
    | LessEqual
    | GreaterEqual
    | IntegerAddition
    | IntegerSubtraction
    | IntegerMultiplication
    | IntegerDivision
    | IntegerRemainder
    | BitShiftRight
    | BitShiftLeft

    (* TODO
    | //WordBitsSelection (Tenary)
    | //WordConcatenation
    | //SwConst
    | //UwConst
    | //WordWidthExtension
    | //WordWidthResize
    | //Union
    | //Inclusion
    | //IfThenElse (Tenary)*)
    
type internal CtlUnaryOperator =
    | LogicalNot
    | ExistsGlobally
    | ExistsNextState
    | ExistsFinally
    | ForallGlobally
    | ForallNext
    | ForallFinally

type internal CtlBinaryOperator =
    | LogicalAnd
    | LogicalOr
    | LogicalXor
    | LogicalNxor
    | LogicalImplies
    | LogicalEquivalence
    | ExistsUntil
    | ForallUntil

type internal LtlUnaryOperator =
    | LogicalNot
    | FutureNext
    | FutureGlobally
    | FutureFinally
    | PastPrevious
    | PastNotPreviousStateNot
    | PastHistorically
    | PastOnce

type internal LtlBinaryOperator =
    | LogicalAnd
    | LogicalOr
    | LogicalXor
    | LogicalNxor
    | LogicalImplies
    | LogicalEquivalence
    | FutureUntil
    | FutureReleases
    | PastSince
    | PastTriggered