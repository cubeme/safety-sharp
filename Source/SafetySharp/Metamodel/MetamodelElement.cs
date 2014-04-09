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
{
	using System;

	/// <summary>
	///     Represents a metamodel element. Metamodel elements are organized as semantically enriched syntax trees during
	///     compilation and code transformation.
	/// </summary>
	/// <remarks>
	///     <para>
	///         There are two different tree types: The formal tree and the extended tree. The extended tree is a view of the
	///         underlying C# syntax and semantic trees, whereas the less sophisticated formal tree is closely aligned with the
	///         underlying formal semantics of the metamodel.
	///     </para>
	///     <para>
	///         The C# syntax tree is first transformed into a tree of extended metamodel elements. Through a series of
	///         transformations, the tree is transformed into a tree of formal metamodel elements only. During the transformation
	///         steps, the tree can contain both extended and formal metamodel elements.
	///     </para>
	///     <para>
	///         Some metamodel elements are shared by both the formal and the extended tree. For instance, there is no difference
	///         for <see cref="Statements.ExpressionStatement" /> elements between both trees, so the code is shared. In other
	///         cases, common
	///         base classes are introduced that allow the step-by-step transformation of extended metamodel elements into formal
	///         metamodel elements. The <see cref="Declarations.MemberDeclaration" /> hierarchy, for example, makes it possible to
	///         transform <see cref="Declarations.FieldDeclaration" /> elements into
	///         <see cref="Declarations.StateVariableDeclaration" /> elements, while <see cref="Declarations.PropertyDeclaration" />
	///         elements are still retained and transformed later on. Once all child elements of the
	///         <see cref="Declarations.ClassDeclaration" /> element have been transformed, the class declaration can itself be
	///         transformed to an <see cref="Declarations.ComponentDeclaration" /> element, for example.
	///     </para>
	/// </remarks>
	public abstract class MetamodelElement
	{
		/// <summary>
		///     Gets the source location of the element.
		/// </summary>
		public SourceLocation SourceLocation { get; private set; }
	}
}