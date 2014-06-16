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

namespace SafetySharp.Metamodel

/// Represents an instantiation of a component field.
type FieldObject = {
    /// The instantiated field symbol.
    FieldSymbol : FieldSymbol

    /// The list of initial values for the field. Each field is guaranteed to have at least one initial value.
    InitialValues : obj list
} 

/// Represents the instantiation of a component.
type ComponentObject = {
    /// The name of the component object. Component object names are unique within a single model object.
    Name : string

    /// The instantiated component symbol.
    ComponentSymbol : ComponentSymbol

    /// Maps each field declared by the component type to a field instantiation.
    Fields : Map<FieldSymbol, FieldObject>

    /// Maps each subcomponent declared by the component type to a component instantiation.
    Subcomponents : Map<ComponentReferenceSymbol, ComponentObject>
} 

/// Represents the instantiation of a partition.
type PartitionObject = {
    /// The instantiated partition symbol.
    //PartitionSymbol : PartitionSymbol TODO

    /// The root component object of the partition.
    RootComponent : ComponentObject
}

/// Represents the instantiation of a model.
type ModelObject = {
    /// The instantiated model symbol.
    //ModelSymbol : ModelSymbol TODO

    /// The partitions the model consists of.
    Partitions : PartitionObject list

    /// Maps each symbol for the component objects declared by the model to the actual component object instance.
    ComponentObjects : Map<ComponentReferenceSymbol, ComponentObject>
} 

/// Represents a configuration of symbols, objects, and formulas that allows a transformation of the model
/// to a modelchecker in order to verify the formulas.
type Configuration = {
    /// The method symbol of the configuration, containing all symbols used throughout the model.
    ModelSymbol : ModelSymbol

    /// The model object of the configuration, containing all partition and component objects used throughout the model.
    ModelObject : ModelObject

    /// The formulas defined over the symbols and objects that require verification.
    Formulas : Formula list

    /// Resolves the body of a component's method.
    MethodBodyResolver : Map<ComponentSymbol * MethodSymbol, Statement>
}