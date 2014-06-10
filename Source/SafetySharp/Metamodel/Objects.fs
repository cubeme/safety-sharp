namespace SafetySharp.Metamodel

/// Represents an instantiation of a component field.
type FieldObject = {
    /// The instantiated field.
    Field : FieldSymbol

    /// The list of initial values for the field. Each field is guaranteed to have at least one initial value.
    InitialValues : obj list
}

/// Represents the instantiation of a component.
type ComponentObject = {
    /// The instantiated component type.
    Component : ComponentSymbol

    Name : string list

    /// Maps each field declared by the component type to a field instantiation.
    Fields : Map<FieldSymbol, FieldObject>

    /// Maps each subcomponent declared by the component type to a component instantiation.
    Subcomponents : Map<SubcomponentSymbol, ComponentObject>
}

// Todo
type [<ReferenceEquality>] ModelObject = {
    X: int
}