namespace SafetySharp.Metamodel

/// Represents statements contained within method bodies.
type Statement =
    /// Represents the empty statement that does nothing.
    | EmptyStatement

    /// Represents a block of statements that are executed sequentially.
    | BlockStatement of Statements : Statement list

    /// Represents a return statement that ends the execution of a method, optionally returning a value.
    | ReturnStatement of Expression : Expression option

    /// Represents a guarded command statement. The body of at most one clause of the guarded command is
    /// executed. For a body to be executed, its guard must evaluate to true. If multiple guards hold, one
    /// clause is chosen nondeterministically.
    | GuardedCommandStatement of (Expression * Statement) list

    /// Represents the assignment of a value to an assignment target, i.e., a field, for instance.
    | AssignmentStatement of Target : Expression * Expression : Expression

/// Maps a method symbol to its method body.
type MethodBodyResolver = Map<MethodSymbol, Statement>