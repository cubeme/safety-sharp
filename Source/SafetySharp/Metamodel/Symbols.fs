namespace SafetySharp.Metamodel

/// Represents the definition of a type.
[<RequireQualifiedAccess>]
type TypeSymbol = 
    /// Represents the type of Boolean values <c>true</c> and <c>false</c>.
    | Boolean

    /// Represents the type of integers.
    | Integer

    /// Represents the type of decimals.
    | Decimal

/// Represents the definition of a field within a component.
type FieldSymbol = {
    /// The name of the field. Field names are unique within a single component and do not overlap
    /// with subcomponent or method names.
    Name : string
    Type : TypeSymbol
}

/// Represents the definition of a method parameter.
type ParameterSymbol = {
    /// The name of the method parameter. Parameter names are unique within a single method.
    Name : string

    /// The type of the method parameter.
    Type : TypeSymbol
}

/// Represents the definition of a method within a component.
type MethodSymbol = {
    /// The name of the method. Method names are unique within a single component and do not overlap
    /// with subcomponent or field names.
    Name : string

    /// The return type of the method.
    ReturnType : TypeSymbol option

    /// The parameters, if any, of the method.
    Parameters : ParameterSymbol list
}

/// Represents the definition of a subcomponent within a parent component.
type SubcomponentSymbol = {
    /// The name of the subcomponent. Subcomponent names are unique within a single component and do
    /// not overlap with field or method names.
    Name : string

    /// The component type of the subcomponent.
    Type : ComponentSymbol
}

/// Represents the type definition of a component within a model.
and ComponentSymbol = { 
    /// The name of the component. Component names are unique within a single model.
    Name : string

    /// The update method of the component, overriding <see cref=\"SafetySharp.Modeling.Component.Update()\" />.
    UpdateMethod : MethodSymbol

    /// The methods declared by the component. The <see cref="UpdateMethod" /> is never contained in this list.
    Methods : MethodSymbol list

    /// The fields declared by the component.
    Fields : FieldSymbol list

    /// The subcomponents declared by the component.
    Subcomponents : SubcomponentSymbol list
}

// TODO
and ModelSymbol = { 
    Fields : FieldSymbol list
}