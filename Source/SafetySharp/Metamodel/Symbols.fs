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
}   with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this

/// Represents the definition of a method parameter.
type ParameterSymbol = {
    /// The name of the method parameter. Parameter names are unique within a single method.
    Name : string

    /// The type of the method parameter.
    Type : TypeSymbol
}   with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this

/// Represents the definition of a method within a component.
type MethodSymbol = {
    /// The name of the method. Method names are unique within a single component and do not overlap
    /// with subcomponent or field names.
    Name : string

    /// The return type of the method.
    ReturnType : TypeSymbol option

    /// The parameters, if any, of the method.
    Parameters : ParameterSymbol list
}   with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this

/// Represents the definition of a subcomponent within a parent component.
type SubcomponentSymbol = {
    /// The name of the subcomponent. Subcomponent names are unique within a single component and do
    /// not overlap with field or method names.
    Name : string
}   with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this

/// Represents the type definition of a component within a model.
type ComponentSymbol = { 
    /// The name of the component. Component names are unique within a single model.
    Name : string

    /// The update method of the component, overriding <see cref="SafetySharp.Modeling.Component.Update()" />.
    UpdateMethod : MethodSymbol

    /// The methods declared by the component. The <see cref="UpdateMethod" /> is never contained in this list.
    Methods : MethodSymbol list

    /// The fields declared by the component.
    Fields : FieldSymbol list

    /// The subcomponents declared by the component.
    Subcomponents : SubcomponentSymbol list
}   with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this

// TODO
and ModelSymbol = { 
    Fields : FieldSymbol list
}
    with

    /// Returns a structured string representation for the current instance.
    override this.ToString () =
        sprintf "%A" this