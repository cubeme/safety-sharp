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
    | AllUntil
    | ExistsUntil

/// Represents a formula that can be modelchecked, for instance.
type Formula =
    /// Represents a state formula that is evaluated in a single model state.
    | StateFormula of StateExpression : Expression

    /// Represents the application of an unary formula operator to a formula.
    | UnaryFormula of Operand : Formula * Operator : UnaryFormulaOperator

    /// Represents the application of a binary formula operator to two subformulas.
    | BinaryFormula of LeftFormula : Formula * Operator : BinaryFormulaOperator * RightFormula : Formula