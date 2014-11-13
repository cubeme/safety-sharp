// Notes:
// 	* SafetySharp uses a lot of FIL. For information how [strict], context, [left], [strict(2)], and [transition] works, see fil.k
//	* "'A`(_;_`)(Parameter1,,Parameter2)" is another form to write down "A(Parameter1;Parameter2)" to omit parsing ambiguities. To escape '(' we write '`)'. To escape '{' we write '`{'
//	* Alternative way to express "(.GuardedCommands => Stmt) ..." is "(.GuardedCommands => Stmt) ~> OtherCalculations:K"

// The semantics document describes a semantics, which is sometimes typed explicitly and sometimes not. For now, this k-Semantics is as a whole not typed explicitly.

module SAFETYSHARP-SYNTAX
// Chapter 2.1: Domains
	syntax Value ::= Bool | Int

// Chapter 2.2: Expressions
	syntax Expr ::=   Id
			| Value
			| Expr "/" Expr		[left,strict]
			| Expr "*" Expr		[left,strict]
			| Expr "%" Expr 	[left,strict]
			> Expr "+" Expr		[left,strict]
			| Expr "-" Expr		[left,strict]
			> Expr "<=" Expr	[left,strict]            
			| Expr "==" Expr	[left,strict]
			| Expr "=/=" Expr	[left,strict]
			| Expr ">=" Expr	[left,strict]
			| Expr ">" Expr		[left,strict]
			| Expr "<" Expr		[left,strict]
			| "!" Expr                  
			> Expr "&&" Expr	[left,strict] 
			> Expr "||" Expr	[left,strict]
			| "(" Expr ")"		[bracket]

// Chapter 2.3: Statements
	syntax GuardedCommand ::= Expr "->>" "{" Stmnt "}"
	
	syntax GuardedCommands ::= List{GuardedCommand,","}

	context ((HOLE ->> { Stmnt:Stmnt }), OtherCandidates:GuardedCommands)

	syntax Stmnt ::= "skip"			// do nothing
			| Id ":=" Expr	[strict(2)]	// assignment to Variable or Field
			| Stmnt ";" Stmnt	[left]	// Sequential Composition
			| GuardedCommands		// Guarded Commands (generalized if-then-else; see wikipedia http://en.wikipedia.org/wiki/Guarded_Command_Language)
			| Id "(" IdList ";" IdList ")"	// Call a required port or a provided port
			| Id "(" ")"			// Call behaviour of sub-component

	syntax LocalVarDecl ::= List{ Id, ","}
	syntax MiniProgram ::= LocalVarDecl ";" Stmnt

	syntax K ::= Stmnt
	syntax K ::= Expr
	syntax KResult ::= Value

// Chapter 3: Component Structure
	// First step is to parse the Component Structure and write its content into the corresponding k-Cells. Most of the syntactic stuff here is only necessary to for this first step and not necessary to describe the details of the semantics. But it cannot be extracted into an own module, because if "syntax Component" is not defined in "module SAFETYSHARP-SYNTAX" (or whatever is defined as syntax-module with "kompile --syntax-module"  it cannot be used in the configuration.
	// TODO: for now I ignore the distinction in the syntax between Declarations and Instantiantions and leave out Types
	
	syntax Component ::= "component" Id "{" Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour "}" // Chapter 3.1.6
//	syntax Component ::= "component" Id //"{" "}"	

	syntax Field ::= Id "=" Values
	syntax RequiredPort ::= Id "r(" TypedParameters ";" TypedParameters ")" //for this untyped semantics: actually the names are not important, just the number of parameters. Actually, if Id is unique, even their number is not important.
	syntax ProvidedPort ::= Id "p(" TypedParameters ";" TypedParameters ")" "{" MiniProgram "}"
	syntax DelayedBinding ::= HierarchicalAccess "<-d-" HierarchicalAccess // First Argument is RequiredPort, second Argument is ProvidedPort
	syntax InstantaneousBinding ::= HierarchicalAccess "<-i-" HierarchicalAccess // First Argument is RequiredPort, second Argument is ProvidedPort
	syntax Binding ::= DelayedBinding | InstantaneousBinding
	syntax ComponentBehaviour ::= "behaviour" "{" MiniProgram "}"

	syntax Components ::= List{Component,""}
	syntax Fields ::= List{Field,""}
	syntax RequiredPorts ::= List{RequiredPort,""}
	syntax ProvidedPorts ::= List{ProvidedPort,""}
	syntax Bindings ::= List{Binding,""}
	syntax Values ::= List{Value,""}
	syntax TypedParameter ::= Id ":" Type
	syntax TypedParameters ::= List{TypedParameter,","}
	syntax Type ::= "bool" | "int"

	syntax HierarchicalAccess ::=	  Id 
					| HierarchicalAccess "." Id		[left]
	syntax K ::= Component
	syntax IdList ::= List{Id,","}
endmodule

module SAFETYSHARP-CONFIGURATION
	imports SAFETYSHARP-SYNTAX

	syntax LoadComponent ::= "#loadRootComponent" "(" Component ")"
	syntax LoadComponent ::= "#loadComponent" "(" Component "," HierarchicalAccess "," Set ")" //second argument is the full Path of the component to load, third argument are the HierarchicalAccesss' of previously loaded Subcomponents of Component
	syntax LoadComponent ::= "#loadFields" "(" HierarchicalAccess "," Fields")"  //First Argument: FullPath of the Component of the Field; Second Argument: A List of Fields
	syntax LoadComponent ::= "#loadProvidedPorts" "(" HierarchicalAccess "," ProvidedPorts ")"
	syntax LoadComponent ::= "#loadRequiredPorts" "(" HierarchicalAccess "," RequiredPorts ")"
	syntax LoadComponent ::= "#loadBindings" "(" HierarchicalAccess "," Bindings ")"  
	
	syntax K ::= LoadComponent

	//TODO: Find better place	
	syntax K ::= "#chooseInitialValue" "(" HierarchicalAccess "," Id ")" //for a specific Field. FullPath to Component, FieldId

	configuration
		<execution>
			// The corresponding elements to the Configuration of Chapter 3.3 in the semantics document are written in "[~= _ ]"
			<loadComponents multiplicity="?"> #loadRootComponent ( $PGM:Component ) </loadComponents>
			<k> .K  </k>	// [~= S \in Stm_{fm}]  (plus initialisation of fields)
			<currentFieldValues> .Map </currentFieldValues>  // (<path>:HierarchicalAccess).FieldName |-> Value. [~= \phi \in \Phi]
			<currentVarValues> .Map </currentVarValues> // (<path>:HierarchicalAccess).VarName |-> Value (without hierarchie). Full Path is needed (TODO: explain why) [~= \varsigma \in \Sigma_{fm}]
			<currentContext> .K </currentContext> // Path to current component (HierarchicalAccess) [~= c^+]
			<gcCurrentCandidates> .Set </gcCurrentCandidates> //Set of possibilities, which can be taken for the next step of a guarded Command (gc)
		</execution>
		<static>
			<component multiplicity="*">
				<path> .K </path> // Type should be HierarchicalAccess. Example n1.n2.n3... where n1=parent(n2), root=n1, n2=parent(n3), 
				<subcomponents> .Set </subcomponents> //Set of paths of subcomponents
				<requiredPort multiplicity="*">
					<rpIdentifier> .K </rpIdentifier>
					<rpInputs> .TypedParameters </rpInputs>
					<rpInouts> .TypedParameters </rpInouts>
				</requiredPort>
				<providedPort multiplicity="*">
					<ppIdentifier> .K </ppIdentifier>
					<ppInputs> .TypedParameters </ppInputs>
					<ppInouts> .TypedParameters </ppInouts>
					<ppCode> .K </ppCode>
				</providedPort>
				<delayedBinding multiplicity="*">
					<dbFromIdentifier> .K </dbFromIdentifier> //From is usually a Provided Port
					<dbToIdentifier> .K </dbToIdentifier> //To is a RequiredPort
				</delayedBinding>
				<instantBinding multiplicity="*">
					<ibFromIdentifier> .K </ibFromIdentifier> //From is usually a Provided Port
					<ibToIdentifier> .K </ibToIdentifier> //To is a RequiredPort
				</instantBinding>
				<field multiplicity="*">
					<fiIdentifier> .K </fiIdentifier>
					<fiPossibleValues> .Values </fiPossibleValues>
				</field>
				<behaviour> .K </behaviour>
			</component>
		</static>




	rule
		<loadComponents>
			#loadRootComponent ( component ComponentName:Id { Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } )
			=>
			#loadComponent ( component ComponentName:Id { Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , ComponentName , .Set ) ... </loadComponents>	[structural]
	
	// loadComponents initially contains the main component, with the following structural rules, we load the components in their corresponding cells in <static> and initialize the main behavior
	rule
		<loadComponents> #loadComponent ( component ComponentName:Id { .Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , FullPath:HierarchicalAccess , SubComponents:Set ) => (#loadFields (FullPath, Fields) ) ~> (#loadRequiredPorts (FullPath, RequiredPorts)) ~> (#loadProvidedPorts (FullPath, ProvidedPorts)) ~> (#loadBindings (FullPath, Bindings))... </loadComponents>
		<static>
			. =>
			<component>
				<path> FullPath </path> //use quoted notation to omit parsing ambiguities
				<subcomponents> SubComponents </subcomponents> 
				<behaviour> ComponentBehaviour </behaviour>
			</component>
			...
		</static>	[structural]

	// extract a subcomponent
	rule
		<loadComponents>
			(#loadComponent ( component ComponentName:Id {(
				component SubComponentName:Id { SubComponentComponents:Components SubComponentFields:Fields SubComponentRequiredPorts:RequiredPorts SubComponentProvidedPorts:ProvidedPorts SubComponentBindings:Bindings SubComponentBehaviour:ComponentBehaviour }

				OtherSubComponents:Components) Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , FullPath:HierarchicalAccess , SubComponents:Set ))
			=>
			(#loadComponent ( component SubComponentName { SubComponentComponents SubComponentFields SubComponentRequiredPorts SubComponentProvidedPorts SubComponentBindings SubComponentBehaviour } , FullPath . SubComponentName, .Set )) // first load the first subcomponent (and thus by recursion all subcomponents)
			~>
			(#loadComponent ( component ComponentName { (OtherSubComponents:Components) Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , FullPath , SetItem( FullPath . SubComponentName) SubComponents ))   // and then the component itself
		...
		</loadComponents>	[structural] //Here we load the SubComponent of a component, thus we need to unwrap a component two times. Hard to read for the first time, but we can spare auxiliary functions, syntax and rules
	

	///// Moving Values into their cells:

	// initialize Fields
	// initialize Fields in the <execution>-Environment
	// variable does not exist in map. We add an entry for the variable in the map with the value as first entry
	//TODO rephrase: case, we already processed all values of one variable.  We also say, that the initial values of this field should be chosen. Because this is a structural rule and choosing an initial value may be indeterministic, we do not choose the Initial Values here. Instead we create a command in the k-Cell to do this work
	rule
		<loadComponents>
			(#loadFields (	FullPath:HierarchicalAccess ,
					(FieldId:Id = (Values:Values ) ) OtherFields:Fields => OtherFields))
			...
		</loadComponents>
		<component>
			<path> FullPath </path>
			(. =><field>
				<fiIdentifier> FieldId </fiIdentifier>
				<fiPossibleValues> Values </fiPossibleValues>
			</field>)
			...
		</component>
		<k>
			.K => #chooseInitialValue( FullPath, FieldId ) ...
		</k>	[structural]

	rule
		<loadComponents>
			(#loadFields ( FullPath:HierarchicalAccess , .Fields ))
			=> . ...
		</loadComponents>	[structural]

	// Initialize Required Ports
	rule
		<loadComponents>
			(#loadRequiredPorts (	FullPath:HierarchicalAccess ,
			('_r`(_;_`)(Identifier:Id,,Inputs:TypedParameters,,Inouts:TypedParameters)) OtherPorts:RequiredPorts => OtherPorts))	// for the meaning of the escaping see note in the beginning
			...
		</loadComponents>
		<component>
			<path> FullPath </path>
			(. => <requiredPort>
				<rpIdentifier> Identifier </rpIdentifier>
				<rpInputs> Inputs </rpInputs>
				<rpInouts> Inouts </rpInouts>
			</requiredPort>)
			...
		</component>	[structural]

	rule
		<loadComponents>
			(#loadRequiredPorts ( FullPath:HierarchicalAccess , .RequiredPorts ))
			=> . ...
		</loadComponents>	[structural]



	// Initialize Provided Ports
	rule
		<loadComponents>
			(#loadProvidedPorts (	FullPath:HierarchicalAccess ,
			('_p`(_;_`)`{_`}(Identifier:Id,,Inputs:TypedParameters,,Inouts:TypedParameters,,Code:MiniProgram)) OtherPorts:ProvidedPorts => OtherPorts))	// for the meaning of the escaping see note in the beginning
			...
		</loadComponents>
		<component>
			<path> FullPath </path>
			(. => <providedPort>
				<ppIdentifier> Identifier </ppIdentifier>
				<ppInputs> Inputs </ppInputs>
				<ppInouts> Inouts </ppInouts>
				<ppCode> Code </ppCode>
			</providedPort>)
			...
		</component>	[structural]

	rule
		<loadComponents>
			(#loadProvidedPorts ( FullPath:HierarchicalAccess , .ProvidedPorts ))
			=> . ...
		</loadComponents>	[structural]

	// Initialize Bindings
	rule
		<loadComponents>
			(#loadBindings ( FullPath:HierarchicalAccess , (ToRequired:HierarchicalAccess <-d- FromProvided:HierarchicalAccess) OtherBindings:Bindings => OtherBindings ))
		</loadComponents>
		<component>
			<path> FullPath </path>
			(. => <delayedBinding>
				<dbFromIdentifier>FromProvided</dbFromIdentifier>
				<dbToIdentifier>ToRequired</dbToIdentifier>
			</delayedBinding>)
			... 
		</component>	[structural]

	rule
		<loadComponents>
			(#loadBindings ( FullPath:HierarchicalAccess , (ToRequired:HierarchicalAccess <-i- FromProvided:HierarchicalAccess) OtherBindings:Bindings => OtherBindings ))
		</loadComponents>
		<component>
			<path> FullPath </path>
			(. => <instantBinding>
				<ibFromIdentifier>FromProvided</ibFromIdentifier>
				<ibToIdentifier>ToRequired</ibToIdentifier>
			</instantBinding>)
			... 
		</component>	[structural]

	rule
		<loadComponents>
			(#loadBindings ( FullPath:HierarchicalAccess , .Bindings ))
			=> . ...
		</loadComponents>	[structural]


	/// Everything done, now load the main Program into the k-Cell
	// We know everything is done, when the <loadComponents>-Cell is empty
	rule
		(<loadComponents> .K </loadComponents> => .)
		<k> ... (.K => "TODO: load program, set Context") </k>		[structural]
		

endmodule

module SAFETYSHARP-SEMANTICS-CONVENIENCE
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION	

	// use of anyValueOf may lead to indeterminism
	syntax Value ::= "anyValueOf" "(" Values ")" [function]
	rule anyValueOf ( Element1:Value Element2:Value Rest:Values ) => anyValueOf ( Element2 Rest)	[transition]
	rule anyValueOf ( Element:Value Rest:Values) => Element	[transition]


endmodule

module SAFETYSHARP-SEMANTICS
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION
	imports SAFETYSHARP-SEMANTICS-CONVENIENCE

	// initialize values (may be indeterministic, indeterminism is hidden in "anyElementOf")
	// leads to (sometimes inconsistent) double assignments in <currentFieldValue>, if value already assigned
	rule
		<k>			
			#chooseInitialValue( FullPath:HierarchicalAccess, FieldId:Id ) => . ...
		</k>
		<component>
			<path> FullPath </path>
			<field>
				<fiIdentifier> FieldId </fiIdentifier>
				<fiPossibleValues> PossibleValues </fiPossibleValues>...
			</field>
			...
		</component>
		<currentFieldValues>
			.Map => (FullPath . FieldId) |-> anyValueOf(PossibleValues) ...
		</currentFieldValues>


// Chapter 2.2: Expressions
	// Common interpretation of Boolean and Arithmetical operators
	rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
	rule I1:Int * I2:Int => I1 *Int I2
	rule I1:Int % I2:Int => I1 modInt I2
	rule I1:Int + I2:Int => I1 +Int I2
	rule I1:Int - I2:Int => I1 -Int I2
	rule I1:Int <= I2:Int => I1 <=Int I2
	rule I1:Int == I2:Int => I1 ==Int I2
	rule I1:Int =/= I2:Int => I1 =/=Int I2
	rule I1:Int >= I2:Int => I1 >=Int I2
	rule I1:Int > I2:Int => I1 >Int I2
	rule I1:Int < I2:Int => I1 <Int I2
	rule ! B:Bool => notBool B 
	rule B1:Bool && B2:Bool => B1 andBool B2
	rule B1:Bool == B2:Bool => B1 ==Bool B2
	rule B1:Bool || B2:Bool => B1 orBool B2
	rule B1:Bool =/= B2:Bool => B1 =/=Bool B2
	
	// Expressions: variable access
	rule
		<k> Var:Id => Val ... </k>
		<currentVarValues> ((Context . Var) |-> Val:Value) ... </currentVarValues>
		<currentContext> Context:HierarchicalAccess </currentContext>

	// Expressions: field access
	rule
		<k> Field:Id => Val ... </k>
		<currentFieldValues>  ((Context . Field) |-> Val:Value) ... </currentFieldValues>
		<currentContext> Context:HierarchicalAccess </currentContext>


	// (skip)
	rule
		<k> skip => . ... </k>
	

	// (assign local variable)
	rule
		<k> (Var:Id := Val:Value) => . ... </k>
		<currentVarValues> ((Context .Var) |-> (OldVal:Value => Val)) ...</currentVarValues>
		<currentContext> Context:HierarchicalAccess </currentContext>

	// (assign field)
	rule
		<k> (Field:Id := Val:Value) => . ... </k>
		<currentFieldValues> ( (Context . Field) |-> (OldVal:Value => Val)) ... </currentFieldValues>
		<currentContext> Context:HierarchicalAccess </currentContext>

	// (seq)
	rule S1:Stmnt ; S2:Stmnt => S1 ~> S2	
	

	// (cmd)
	// 4 Steps to evaluate a GuardedCommand
	//   * 1)  evaluate the guard of the first GuardedCommand in the current Cell (done by [strict(1)])
	//   * 2a) if this guard is false, throw away the first GuardedCommand
	//   * 2b) if this guard is true, put the Command into the list of gcCurrentCandidates
	//   * 3) Repeat until all GuardedCommands are evaluated
	//   * 4)  When every GuardedCommand is evaluated, the current k-Cell contains .GuardedCommands. Now replace .GuardedCommands with any candidate from the list and delete all candidates

	rule
		<k> ((false ->> { Stmt:Stmnt } ) , OtherCandidates:GuardedCommands) => OtherCandidates  ... </k>

	rule
		<k> ((true ->> { Stmt:Stmnt } ) , OtherCandidates:GuardedCommands) => OtherCandidates  ... </k>
		<gcCurrentCandidates> (.Set => SetItem(Stmt) ) OtherSuccessfulCandidates:Set </gcCurrentCandidates>
	
	rule
		<k> (.GuardedCommands => Stmt) ... </k>
		<gcCurrentCandidates> (SetItem(Stmt) => .Set ) (OtherSuccessfulCandidates:Set => .Set) </gcCurrentCandidates> [transition]

	// (call)
	
/*
	// (beh)

	//TODO: Convenience Functions for (call) and (beh)
	rule
		<currentVarValues> .Map </currentVarValues> //TODO: Important: Full Path is used for local variables, because current var Values need to be conserved and must be accessible, when (beh) or (call) returns! TODO: Write Test, which tests it
		<k> (SubComponentId:Id) ( ) => . ... </k>
		<currentContext> CurrentContext:HierarchicalAccess => ( CurrentContext . SubComponentId ) </currentContext>
		<component>
			<path> ( CurrentContext . SubComponentId ) </path>
			<behaviour>  </behaviour>
			...
		</component>
*/

endmodule


module SAFETYSHARP
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION
	
	// if you just want to know how initialization of all cells works and looks like for a specific program, just comment out the following line
	imports SAFETYSHARP-SEMANTICS

endmodule
