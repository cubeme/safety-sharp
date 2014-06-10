namespace SafetySharp.Metamodel

/// Represents the operator of an unary temporal formula.
type UnaryFormulaOperator =
    // Non-temporal operators
    | Not

    // LTL temporal operators
    | Next
    | Finally
    | Globally

    // CTL temporal operators
    | AllPathsNext
    | AllPathsFinally
    | AllPathsGlobally
    | ExistsPathNext
    | ExistsPathFinally
    | ExistsPathGlobally

/// Represents the operator of a binary formula.
type BinaryFormulaOperator =
    // Non-temporal operators
    | And
    | Or
    | Implication
    | Equivalence

    // LTL temporal operator
    | Until

    // CTL temporal operators
    | AllPathsUntil
    | ExistsPathUntil

/// Represents a formula that can be modelchecked, for instance.
type Formula =
    /// Represents a state formula that is evaluated in a single model state.
    | StateFormula of StateExpression : Expression

    /// Represents the application of an unary formula operator to a formula.
    | UnaryFormula of Operand : Formula * Operator : UnaryFormulaOperator

    /// Represents the application of a binary formula operator to two subformulas.
    | BinaryFormula of LeftFormula : Formula * Operator : BinaryFormulaOperator * RightFormula : Formula

    with 

    /// Gets a value indicating whether the formula is a valid linear temporal logic formula.
    member this.IsLtl () = 
        match this with
        | StateFormula _ -> 
            true
        | UnaryFormula (operand, operator) ->
            (operator = Not || operator = Next || operator = Finally || operator = Globally) && operand.IsLtl ()
        | BinaryFormula (left, operator, right) ->
            operator <> AllPathsUntil && operator <> ExistsPathUntil && left.IsLtl () && right.IsLtl ()

    /// Gets a value indicating whether the formula is a valid computation tree logic formula.
    member this.IsCtl () = 
        match this with
        | StateFormula _ -> 
            true
        | UnaryFormula (operand, operator) ->
            operator <> Next && operator <> Finally && operator <> Globally && operand.IsCtl ()
        | BinaryFormula (left, operator, right) ->
            operator <> Until && left.IsCtl () && right.IsCtl ()