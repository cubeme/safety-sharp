namespace SafetySharp.Metamodel

open SafetySharp.Utilities

/// Represents an instantiation of a component field.
type [<ReferenceEquality>] FieldObject = {
    /// The instantiated field.
    Field : FieldSymbol

    /// The list of initial values for the field. Each field is guaranteed to have at least one initial value.
    InitialValues : obj list
}

/// Represents the instantiation of a component.
type [<ReferenceEquality>] ComponentObject = {
    /// The instantiated component type.
    Component : ComponentSymbol

    /// Maps each field declared by the component type to a field instantiation.
    Fields : Dictionary<FieldSymbol, FieldObject>

    /// Maps each subcomponent declared by the component type to a component instantiation.
    Subcomponents : Dictionary<SubcomponentSymbol, ComponentObject>
}

// Todo
type [<ReferenceEquality>] ModelConfigurationObject = {
    X: int
}