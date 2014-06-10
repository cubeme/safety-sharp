namespace NuXmvDataStructures.Ast

type UnaryOperator = 
    | LogicalNot

type BinaryOperator=      
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
    
type CtlUnaryOperator =
    | LogicalNot
    | ExistsGlobally
    | ExistsNextState
    | ExistsFinally
    | ForallGlobally
    | ForallNext
    | ForallFinally

type CtlBinaryOperator =
    | LogicalAnd
    | LogicalOr
    | LogicalXor
    | LogicalNxor
    | LogicalImplies
    | LogicalEquivalence
    | ExistsUntil
    | ForallUntil

type LtlUnaryOperator =
    | LogicalNot
    | FutureNext
    | FutureGlobally
    | FutureFinally
    | PastPrevious
    | PastNotPreviousStateNot
    | PastHistorically
    | PastOnce

type LtlBinaryOperator =
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