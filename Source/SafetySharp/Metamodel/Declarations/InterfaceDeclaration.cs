using System;

namespace SafetySharp.Metamodel.Declarations
{
	using Modeling;

	/// <summary>
	///     Represents the declaration of a component interface.
	/// </summary>
	partial class InterfaceDeclaration
	{
		/// <summary>
		///     Represents the empty base component interface corresponding to <see cref="IComponent" />.
		/// </summary>
		public static readonly InterfaceDeclaration BaseInterface = new InterfaceDeclaration(
			new Identifier(typeof(IComponent).FullName));

		/// <summary>
		///     Gets a value indicating whether the current instance represents the <see cref="Component" /> class.
		/// </summary>
		public bool IsBaseInterface
		{
			get { return this == BaseInterface; }
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			return String.Format("Interface '{0}'", Identifier);
		}
	}
}