namespace SafetySharp.Metamodel

/// Represents the operator in an unary expression.
type UnaryOperator =
    | Minus
    | LogicalNot

/// Represents the operator in a binary expression.
type BinaryOperator =
    // Arithmetic operators
    | Add
    | Subtract
    | Multiply
    | Divide
    | Modulo
    
    // Logical operators
    | LogicalAnd
    | LogicalOr
    
    // Equality operators
    | Equals
    | NotEquals
    
    // Comparison operators
    | LessThan
    | LessThanOrEqual
    | GreaterThan
    | GreaterThanOrEqual

/// Represents side-effect free expressions within modeling programs.
type Expression =
    /// Represents a Boolean literal, that is, either <c>true</c> or <c>false</c>.
    | BooleanLiteral of Value : bool

    /// Represents an integer value.
    | IntegerLiteral of Value : int

    /// Represents a decimal value.
    | DecimalLiteral of Value : decimal

    /// Represents the application of an unary operator to an expression.
    | UnaryExpression of Operand : Expression * Operator : UnaryOperator

    /// Represents the application of a binary operator to two subexpressions.
    | BinaryExpression of LeftExpression : Expression * Operator : BinaryOperator * RightExpression : Expression

    /// Represents a field access, either for reading or writing.
    | FieldAccessExpression of Field : FieldSymbol