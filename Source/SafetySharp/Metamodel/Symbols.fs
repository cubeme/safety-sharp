// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Internal.Metamodel

/// Represents the definition of a type.
[<RequireQualifiedAccess>]
type internal TypeSymbol = 
    /// Represents the type of Boolean values <c>true</c> and <c>false</c>.
    | Boolean

    /// Represents the type of integers.
    | Integer

    /// Represents the type of decimals.
    | Decimal

/// Represents the definition of a field within a component.
type internal FieldSymbol = {
    /// The name of the field. Field names are unique within a single component and do not overlap
    /// with subcomponent or method names.
    Name : string

    /// The type of the field.
    Type : TypeSymbol
} 

/// Represents the definition of a local variable within a statement block.
type internal LocalSymbol = {
    /// The name of the local variable. Local variable names do not overlap with method parameter names.
    Name : string

    /// The type of the field.
    Type : TypeSymbol
} 

/// Represents the definition of a method parameter.
type internal ParameterSymbol = {
    /// The name of the method parameter. Parameter names are unique within a single method and do not overlap
    /// with local variable names.
    Name : string

    /// The type of the method parameter.
    Type : TypeSymbol
} 

/// Represents the definition of a method within a component.
type internal MethodSymbol = {
    /// The name of the method. Method names are unique within a single component and do not overlap
    /// with subcomponent or field names.
    Name : string

    /// The return type of the method.
    ReturnType : TypeSymbol option

    /// The parameters, if any, of the method.
    Parameters : ParameterSymbol list

    /// The local varaibles, if any, of the method.
    Locals : LocalSymbol list
} 

/// Represents the definition of a provided port within a component.
type internal ProvidedPortSymbol = ProvidedPort of MethodSymbol

/// Represents the definition of a required port within a component.
type internal RequiredPortSymbol = RequiredPort of MethodSymbol

/// Represents the type definition of a component within a model.
type internal ComponentSymbol = { 
    /// The name of the component. Component names are unique within a single model.
    Name : string

    /// The update method of the component, overriding <see cref="SafetySharp.Modeling.Component.Update()" />.
    UpdateMethod : MethodSymbol option

    /// The provided ports declared by the component.
    ProvidedPorts : ProvidedPortSymbol list

    /// The required ports declared by the component.
    RequiredPorts : RequiredPortSymbol list

    /// The fields declared by the component.
    Fields : FieldSymbol list
}

/// Represents the definition of a subcomponent within a parent component or model.
type internal ComponentReferenceSymbol = {
    /// The name of the component reference. Component reference names are unique within a single component or model and do
    /// not overlap with field or method names.
    Name : string

    /// The referenced component symbol.
    ComponentSymbol : ComponentSymbol
} 

/// Represents the type definition of a partition within a model.
type internal PartitionSymbol = {
    /// The name of the partition. Within a single model, the partition name is unique.
    Name : string

    /// The symbol of the partition's root component.
    RootComponent : ComponentSymbol

    // TODO: Ports and port bindings
}

/// Represents the type definition of a model.
type internal ModelSymbol = { 
    /// The partitions the model consists of.
    Partitions : PartitionSymbol list

    /// The component symbols defined in the model.
    ComponentSymbols : ComponentSymbol list

    /// Maps each component symbol to its list of subcomponent symbols. 
    /// Note: The subcomponent relationships have to be stored outside of the individual component symbols in order to 
    /// break a cyclic dependency during symbol construction.
    Subcomponents : Map<ComponentSymbol, ComponentReferenceSymbol list>

    /// The symbols for the component objects declared by the model.
    ComponentObjects : ComponentReferenceSymbol list
} 
