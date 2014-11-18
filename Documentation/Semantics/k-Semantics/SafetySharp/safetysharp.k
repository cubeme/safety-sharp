// Notes:
// 	* SafetySharp uses a lot of FIL. For information how [strict], context, [left], [strict(2)], and [transition] works, see fil.k
//	* "'A`(_;_`)(Parameter1,,Parameter2)" is another form to write down "A(Parameter1;Parameter2)" to omit parsing ambiguities. To escape '(' we write '`)'. To escape '{' we write '`{'
//	* Alternative way to express "(.GuardedCommands => Stmt) ..." is "(.GuardedCommands => Stmt) ~> OtherCalculations:K"
//	* Starting with k-Framework release 3.4.1 (not officially released yet), the map operations could be expressed more concisely
//	* When two different cells are written down (in his example two times <component>), k assumes, that these _are_ actually different cells, so we have to write a rule for the case, when it is actually one cell
// The semantics document describes a semantics, which is sometimes typed explicitly and sometimes not. For now, this k-Semantics is as a whole not typed explicitly.

module SAFETYSHARP-SYNTAX
// Chapter 2.1: Domains
	syntax Value ::= Bool | Int | "#failureElement" | "#missingElement"

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
			| Id "(" ExprList ";" IdList ")"	[strict(2)] // Call a required port or a provided port, expressions should be evaluated first
			| Id "(" ")"			// Call behaviour of sub-component

	syntax ExprList ::= List{Expr,","}	[strict]	//List of expressions should be evaluated automatically, when a list like this appears in the first k-Cell. Todo: Rename to Exprs to remain consistent
	
	syntax MiniProgram ::= TypedVarDeclarations ";" Stmnt

	syntax K ::= Stmnt
	syntax K ::= Expr
	syntax KResult ::= Value

// Chapter 3: Component Structure
	// First step is to parse the Component Structure and write its content into the corresponding k-Cells. Most of the syntactic stuff here is only necessary to for this first step and not necessary to describe the details of the semantics. But it cannot be extracted into an own module, because if "syntax Component" is not defined in "module SAFETYSHARP-SYNTAX" (or whatever is defined as syntax-module with "kompile --syntax-module"  it cannot be used in the configuration.
	// TODO: for now I ignore the distinction in the syntax between Declarations and Instantiantions and leave out Types
	
	syntax Component ::= "component" Id "{" Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour "}" // Chapter 3.1.6
//	syntax Component ::= "component" Id //"{" "}"	

	syntax Field ::= Id "=" Values
	syntax RequiredPort ::= Id "r(" TypedVarDeclarations ";" TypedVarDeclarations ")" //for this untyped semantics: actually the names are not important, just the number of parameters. Actually, if Id is unique, even their number is not important.
	syntax ProvidedPort ::= Id "p(" TypedVarDeclarations ";" TypedVarDeclarations ")" "{" MiniProgram "}"
	syntax DelayedBinding ::= BindingLink "<-d-" BindingLink // First Argument is RequiredPort, second Argument is ProvidedPort
	syntax InstantaneousBinding ::= BindingLink "<-i-" BindingLink // First Argument is RequiredPort, second Argument is ProvidedPort
	syntax Binding ::= DelayedBinding | InstantaneousBinding
	syntax ComponentBehaviour ::= "behaviour" "{" MiniProgram "}"

	syntax Components ::= List{Component,""}
	syntax Fields ::= List{Field,""}
	syntax RequiredPorts ::= List{RequiredPort,""}
	syntax ProvidedPorts ::= List{ProvidedPort,""}
	syntax Bindings ::= List{Binding,""}
	syntax Values ::= List{Value,""}
	syntax TypedVarDeclaration ::= Id ":" Type
	syntax TypedVarDeclarations ::= List{TypedVarDeclaration,","}
	syntax Type ::= "bool" | "int"

	syntax BindingLink ::=	  Id		// reference to port named Id in this Component
				| Id "." Id	// reference to port named Id (second) in subcomponent named Id (first)

	syntax Path ::=	  Id 
					| Path "." Id		[left]
	
	syntax K ::= Component
	syntax IdList ::= List{Id,","}	//TODO: Rename to Ids to remain consistent
endmodule

module SAFETYSHARP-CONFIGURATION
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-SEMANTICS-CONVENIENCE

	syntax LoadComponent ::= "#loadRootComponent" "(" Component ")"
	syntax LoadComponent ::= "#loadComponent" "(" Component "," Path "," Set ")" //second argument is the full Path of the component to load, third argument are the Paths' of previously loaded Subcomponents of Component
	syntax LoadComponent ::= "#loadFields" "(" Path "," Fields")"  //First Argument: FullPath of the Component of the Field; Second Argument: A List of Fields
	syntax LoadComponent ::= "#loadProvidedPorts" "(" Path "," ProvidedPorts ")"
	syntax LoadComponent ::= "#loadRequiredPorts" "(" Path "," RequiredPorts ")"
	syntax LoadComponent ::= "#loadBindings" "(" Path "," Bindings ")"  
	
	syntax K ::= LoadComponent

	//TODO: Find better place	
	syntax K ::= "#chooseInitialValue" "(" Path "," Id ")" //for a specific Field. FullPath to Component, FieldId

	configuration
		<execution>
			// The corresponding elements to the Configuration of Chapter 3.3 in the semantics document are written in "[~= _ ]"
			<loadComponents multiplicity="?"> #loadRootComponent ( $PGM:Component ) </loadComponents>
			<k> .K  </k>	// [~= S \in Stm_{fm}]  (plus initialisation of fields)
			<currentFieldValues> .Map </currentFieldValues>  // (<path>:Path).FieldName |-> Value. [~= \phi \in \Phi]
			<currentVarValues> .Map </currentVarValues> // (<path>:Path).VarName |-> Value (without hierarchie). Full Path is needed (TODO: explain why) [~= \varsigma \in \Sigma_{fm}]
			<currentComponent> .K </currentComponent> // Path to current component (Path) [~= c^+]
			<currentCall> .K </currentCall>
			<gcCurrentCandidates> .Set </gcCurrentCandidates> //Set of possibilities, which can be taken for the next step of a guarded Command (gc)
		</execution>
		<static>
			// Extracting the bindings from the component-hierarchy makes the semantics easier to read. Formerly, when bindings had their cell in the bindings, there were several restrictions, where bindings in the source file could be declared. Also it shrank down the number of rules to call a required port. Now we only need to differentiate between two cases (required port in the same component vs. in a different component) for delayed ports. E.g. it was not that easy to connect in component c1 the required port p1 of c1.c2 to provided port p2 of c1.c2.
			// And it also fits to the idea that components are declared independent from bindings and bindings are "injected" afterwards.
			<instantBindings> .Map </instantBindings>	// component1:Path @ to_required:Id |-> component2:Path @ from_provided:Id
			<delayedBindings> .Map </delayedBindings>	// component1:Path @ to_required:Id |-> component2:Path @ from_provided:Id
			<component multiplicity="*">
				<path> .K </path> // Type should be Path. Example n1.n2.n3... where n1=parent(n2), root=n1, n2=parent(n3), 
				<subcomponents> .Set </subcomponents> //Set of paths of subcomponents
				<requiredPort multiplicity="*">
					<rpIdentifier> .K </rpIdentifier>
					<rpInputs> .TypedVarDeclarations </rpInputs>
					<rpInouts> .TypedVarDeclarations </rpInouts>
				</requiredPort>
				<providedPort multiplicity="*">
					<ppIdentifier> .K </ppIdentifier>
					<ppInputs> .TypedVarDeclarations </ppInputs>
					<ppInouts> .TypedVarDeclarations </ppInouts>
					<ppCode> .K </ppCode>
				</providedPort>
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
		<loadComponents> #loadComponent (
				component ComponentName:Id {
					.Components
					Fields
					RequiredPorts
					ProvidedPorts
					Bindings
					behaviour { ComponentBehaviour }
				} ,
				FullPath:Path , SubComponents:Set ) => (#loadFields (FullPath, Fields) ) ~> (#loadRequiredPorts (FullPath, RequiredPorts)) ~> (#loadProvidedPorts (FullPath, ProvidedPorts)) ~> (#loadBindings (FullPath, Bindings))... </loadComponents>
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

				OtherSubComponents:Components) Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , FullPath:Path , SubComponents:Set ))
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
			(#loadFields (	FullPath:Path ,
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
			(#loadFields ( FullPath:Path , .Fields ))
			=> . ...
		</loadComponents>	[structural]

	// Initialize Required Ports
	rule
		<loadComponents>
			(#loadRequiredPorts (	FullPath:Path ,
			('_r`(_;_`)(Identifier:Id,,Inputs:TypedVarDeclarations,,Inouts:TypedVarDeclarations)) OtherPorts:RequiredPorts => OtherPorts))	// for the meaning of the escaping see note in the beginning
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
			(#loadRequiredPorts ( FullPath:Path , .RequiredPorts ))
			=> . ...
		</loadComponents>	[structural]



	// Initialize Provided Ports
	rule
		<loadComponents>
			(#loadProvidedPorts (	FullPath:Path ,
			('_p`(_;_`)`{_`}(Identifier:Id,,Inputs:TypedVarDeclarations,,Inouts:TypedVarDeclarations,,Code:MiniProgram)) OtherPorts:ProvidedPorts => OtherPorts))	// for the meaning of the escaping see note in the beginning
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
			(#loadProvidedPorts ( FullPath:Path , .ProvidedPorts ))
			=> . ...
		</loadComponents>	[structural]

	// Initialize Bindings
	rule
		<loadComponents>
			(#loadBindings ( FullPath:Path , (ToRequired:BindingLink <-d- FromProvided:BindingLink) OtherBindings:Bindings => OtherBindings ))
		</loadComponents>
		<delayedBindings>
			(.Map => (FullPath @ ToRequired) |-> (FullPath @ FromProvided) )
			OtherAlreadyAddedBindings:Map
		</delayedBindings>	[structural]

	rule
		<loadComponents>
			(#loadBindings ( FullPath:Path , (ToRequired:BindingLink <-i- FromProvided:BindingLink) OtherBindings:Bindings => OtherBindings ))
		</loadComponents>
		<instantBindings>
			(.Map => (FullPath @ ToRequired) |-> (FullPath @ FromProvided) )
			OtherAlreadyAddedBindings:Map
		</instantBindings>	[structural]

	rule
		<loadComponents>
			(#loadBindings ( FullPath:Path , .Bindings ))
			=> . ...
		</loadComponents>	[structural]


	/// Everything done, now load the main Program into the k-Cell
	// We know everything is done, when the <loadComponents>-Cell is empty
	// this is somehow the main()-method
	rule
		(<loadComponents> .K </loadComponents> => .)
		<component>
			<path> Component:Id </path> // the only component, which has an Id as path (and not a more level Path), is the main component
			<behaviour> LocalVars:TypedVarDeclarations ; Code:Stmnt </behaviour>
			...
		</component>
		<currentVarValues> .Map => freshVarEntries ( .Map , Component , LocalVars ) </currentVarValues>
		<currentComponent> .K => Component </currentComponent>
		<k> (.K => Code ) </k>		[structural]
		

endmodule

module SAFETYSHARP-SEMANTICS-CONVENIENCE
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION	

	// use of anyValueOf may lead to indeterminism
	syntax Value ::= "anyValueOf" "(" Values ")" [function]
	rule anyValueOf ( Element1:Value Element2:Value Rest:Values ) => anyValueOf ( Element2 Rest)	[transition]
	rule anyValueOf ( Element:Value Rest:Values) => Element	[transition]
	
	/*
	//((Context . Var) |-> Val:Value)
	syntax Map ::= "removeVarEntries" "(" Map "," Path "," TypedVarDeclarations ")"	[function] //Map to delete entries from; prefix of Path, which values should be deleted; Variables to delete

	rule removeVarEntries ( ((Path . Var) |-> Value:Value ) FieldMap:Map => FieldMap, Path:Path , (Var:Id : Type:Type) , OtherParameter:TypedVarDeclarations => OtherParameter)
	rule removeVarEntries ( FieldMap:Map , Path:Path , (Var:Id : Type:Type) , OtherParameter:TypedVarDeclarations => OtherParameter)	when notBool ((Path . Var) in keys(FieldMap)) 
	rule removeVarEntries ( FieldMap:Map , Path:Path , .TypedVarDeclarations ) => FieldMap
	*/	

	syntax Map ::= "freshVarEntries" "(" Map "," Path "," TypedVarDeclarations ")"	[function] //Map to delete entries from; prefix of Path, which values should be deleted; Variables to delete

	rule freshVarEntries ( ((Path . Var) |-> (Value:Value => #missingElement ) ) FieldMap:Map , Path:Path , ((Var:Id : Type:Type) , OtherParameter:TypedVarDeclarations => OtherParameter))
	rule freshVarEntries (( .Map => (Path . Var) |-> #missingElement ) FieldMap:Map , Path:Path , ( (Var:Id : Type:Type) , OtherParameter:TypedVarDeclarations => OtherParameter))	when notBool ((Path . Var) in keys(FieldMap)) 
	rule freshVarEntries ( FieldMap:Map , Path:Path , .TypedVarDeclarations ) => FieldMap
		
	syntax Map ::= "copyEntries" "("
				Map ","
				"source:" Path "," IdList ","
				"target:" Path "," IdList ")"	[function]
	rule copyEntries (	( ( ToContext . ToId) |-> (OldValue => NewValue) ) ( ( FromContext . FromId) |-> NewValue:Value ) FieldMap:Map,
				source:  FromContext:Path , (FromId:Id , OtherFroms => OtherFroms),
				target:  ToContext:Path   , (ToId:Id , OtherTos => OtherTos))
	rule copyEntries (	( .Map => ( ( ToContext . ToId) |-> NewValue )) ( ( FromContext . FromId) |-> NewValue:Value ) FieldMap:Map,
				source:  FromContext:Path , (FromId:Id , OtherFroms => OtherFroms),
				target:  ToContext:Path   , (ToId:Id , OtherTos => OtherTos))	when notBool ((ToContext . ToId) in keys(FieldMap)) 
	rule copyEntries (	FieldMap:Map ,
				source:  FromContext:Path , .IdList ,
				target:  FromContext:Path , .IdList ) => FieldMap

	syntax Map ::= "assignValues" "("
				Map ","
				"values:" ExprList "," // ExprList should be already evaluated Expressions (thus a list of Values)
				"target:" Path "," IdList ")"	[function]
	rule assignValues (	( ( ToContext . Var) |-> (OldValue => Value) ) FieldMap:Map ,
				values:  (( Value:Value , OtherExprs:ExprList ) => OtherExprs),
				target:  ToContext:Path , (Var:Id  , OtherVars:IdList => OtherVars ) )
	rule assignValues (	( .Map => ( ( ToContext . Var) |->  Value) ) FieldMap:Map ,
				values:  (( Value:Value , OtherExprs:ExprList ) => OtherExprs),
				target:  ToContext:Path , (Var:Id  , OtherVars:IdList => OtherVars ) )	when notBool ((ToContext . Var) in keys(FieldMap))

	rule assignValues (	FieldMap:Map ,
				values:  .ExprList ,
				target:  ToContext:Path , .IdList ) => FieldMap

	syntax IdList ::= "extractIds" "(" TypedVarDeclarations ")" [function]

	rule extractIds ( ( Id:Id : Type:Type ) , OtherVars:TypedVarDeclarations) => (Id , extractIds ( OtherVars ) )

	rule extractIds ( .TypedVarDeclarations ) => .IdList


	syntax Path ::= Path "@" BindingLink [function] // Path:Path @@ Link:BindingLink
	rule Path:Path @ PortName:Id => Path . PortName
	rule Path:Path @ (SubComponent:Id . PortName:Id)  => (Path . SubComponent) . PortName

endmodule

module SAFETYSHARP-SEMANTICS
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION
	imports SAFETYSHARP-SEMANTICS-CONVENIENCE

	// initialize values (may be indeterministic, indeterminism is hidden in "anyElementOf")
	// leads to (sometimes inconsistent) double assignments in <currentFieldValue>, if value already assigned
	rule
		<k>			
			#chooseInitialValue( FullPath:Path, FieldId:Id ) => . ...
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
		<currentVarValues> (((CurrentComponent . CurrentCall) . Var) |-> Val:Value) ... </currentVarValues>
		<currentComponent> CurrentComponent:Path </currentComponent>
		<currentCall> CurrentCall:Id </currentCall>  //called from provided

	rule
		<k> Var:Id => Val ... </k>
		<currentVarValues> ((CurrentComponent . Var) |-> Val:Value) ... </currentVarValues>
		<currentComponent> CurrentComponent:Path </currentComponent>
		<currentCall> .K </currentCall>	//called from behaviour



	// Expressions: field access
	rule
		<k> Field:Id => Val ... </k>
		<currentFieldValues>  ((CurrentComponent . Field) |-> Val:Value) ... </currentFieldValues>
		<currentComponent> CurrentComponent:Path </currentComponent>


	// (skip)
	rule
		<k> skip => . ... </k>
	

	// (assign local variable)
	rule
		<k> (Var:Id := Val:Value) => . ... </k>
		<currentVarValues> (((CurrentComponent . CurrentCall) . Var) |-> (OldVal:Value => Val)) ...</currentVarValues>
		<currentComponent> CurrentComponent:Path </currentComponent>
		<currentCall> CurrentCall:Id </currentCall> //called from provided

	rule
		<k> (Var:Id := Val:Value) => . ... </k>
		<currentVarValues> ((CurrentComponent . Var) |-> (OldVal:Value => Val)) ...</currentVarValues>
		<currentComponent> CurrentComponent:Path </currentComponent>
		<currentCall> .K </currentCall>	//called from behaviour

	// (assign field)
	rule
		<k> (Field:Id := Val:Value) => . ... </k>
		<currentFieldValues> ( (CurrentComponent . Field) |-> (OldVal:Value => Val)) ... </currentFieldValues>
		<currentComponent> CurrentComponent:Path </currentComponent>

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


	// (call) and (beh)
	// There are three possible ways to implement these rules:
	//	1) change the configuration to look somehow like that and create two rules: The first creates a new execution-Context and the second removes this context, when calculation is done
	//		<currentComponent> .Path </currentComponent>
	//		<execution mulitplicity="*">
	//			<contextPath> . Path </contextPath>
	//		</execution>
	//	   Pros:
	//		+ resembles the written semantics more closely
	//		+ allows implementation of recursion
	//		+ could also be used to describe (seq)-Rule
	//	   Cons:
	//		- overkill, makes semantics harder to read
	//	   Idea how to implement:
	//		When one of the rules (seq), (cmd), (call), (beh), recognizes, it needs a
	//		new execution environment, which does not exist, create it with needed program in its k-Cell. When it recognizes, that the environment exists and its k-Cell is empty, use its results and remove the environment.
	//	2) change the way local variables work: Only one global map for variables. When a new variable-context for (call) or (beh) is needed, prefix the corresponding key of this variable in the map <currentVarValues> with the path of the component and the function-call hierarchy. Also introduce an element in <execution> for the function-call hierarchy. When a function is called, all its current values are flushed away in <currentVarValues>. Also need to adapt the rule (assign_v) and the rule (getting the value of a variable in an expression) )
	//	   Pros:
	//		+ allows implementation of recursion
	//		+ semantics easier to read
	//		+ easier to implement here in k
	//		+ transformation of the model checker also needs to do something similar,
	//		  because variables cannot be introduced there arbitrarily
	//	3) change the way local variables work: But in contrast to way 2 do not keep trac of the function-call hierarchy. This leads to way less variables in the <currentVarValues>-map, but it also disallows recursion.
	//	   Pros:
	//		+ easy to implement and read
	//		+ no "stack" required
	//	   Cons:
	//		- less powerful (no recursion; that means also no "hidden" recursion, where a provided port calls a required port, which links to the same required port )
	//		- further away from regular imperative programming languages
	// In this file we implemented way 3
	
	// TODO: If a delayed binding gets called more times? Need to keep track of the execution call -> add to configuration
	
	// Bindings are done in a slightly different way compared to the semantics document.
	// Here we use the current component always as reference

	// We ensure on the call of a behaviour or a port, that all variables which might be accessed are "fresh"

	// (call)
	// This is a call of a Required Port. Provided Ports cannot be called (according to the full semantics)
	// We split up the call into two rules. TODO: describe
	// Because we applied the [strict] rules on the call-Statment and the ExprList, the Inputs are already evaluated, when this Statement appears in the first k-Cell
	syntax K ::= "#restoreContextAndWriteBackVariables" "(" 
			"from:" IdList "," // SourceInouts:TypedVarDeclarations
			"to:" Path "," K "," IdList ")" // ( Component:Path , Call:K , TargetInouts:TypedVarDeclarations

	// (call instantaneous)
	//	* RequiredPortComponent = ProvidedPortComponent (= CurrentComponent)
	// 	* parent(RequiredPortComponent) = ProvidedPortComponent)
	// 	* parent(RequiredPortComponent) = parent(ProvidedPortComponent; RequiredPortComponent!=ProvidedPortComponent)
	// 	* RequiredPortComponent = parent(ProvidedPortComponent)
	// CurrentComponent = RequiredPortContext
	// could be called in a behaviour or in a provided port
	// Context depends on Component and Call
	rule
		<k> 
			(RequiredPortName:Id ( InputValues:ExprList ; InoutsOfCurrentContext:IdList ))
			=>
			CodeOfProvidedPort ~>
			#restoreContextAndWriteBackVariables (
				from: extractIds(InoutsOfNextContext) ,
				to:   CurrentComponent, CurrentCall , InoutsOfCurrentContext)
			...
		</k>
		<currentCall> CurrentCall:K => ProvidedPortName </currentCall>
		<currentComponent> CurrentComponent:Path => ProvidedPortComponent </currentComponent>
		<instantBindings> ( (CurrentComponent . RequiredPortName) |-> (ProvidedPortComponent:Path . ProvidedPortName:Id ) ) OtherBindings:Map </instantBindings>
		<component>
			<path> ProvidedPortComponent </path>
			<providedPort multiplicity="*">
				<ppIdentifier> ProvidedPortName </ppIdentifier>
				<ppInputs> PpInputs:TypedVarDeclarations </ppInputs>
				<ppInouts> InoutsOfNextContext:TypedVarDeclarations </ppInouts>
				<ppCode> LocalVars:TypedVarDeclarations ; CodeOfProvidedPort:Stmnt </ppCode>
			</providedPort>
			...
		</component>
		<currentVarValues> CurrentValuation:Map =>
			// first copy inputs and inouts, then set every local entry to the #missingElement
			freshVarEntries(
					copyEntries( //inouts
						assignValues (	//inputs
							CurrentValuation,
							values: InputValues , // InputValues have already been evaluated (because we declared the call-expression as strict)
							target: ( ProvidedPortComponent . ProvidedPortName ) , extractIds(PpInputs)
						),
						source: (CurrentComponent @ CurrentCall ) , InoutsOfCurrentContext ,
						target: ( ProvidedPortComponent . ProvidedPortName ) , extractIds(InoutsOfNextContext)
					)
					, ( ProvidedPortComponent . ProvidedPortName ), LocalVars )
		</currentVarValues>


	// (call (part write-back))
	// Note: The context is different from the context of
	rule
		<k> #restoreContextAndWriteBackVariables (
				from: SourceInouts:IdList ,
				to:   BackToComponent:Path , BackToCall:K , TargetInouts:IdList) => .K ... </k>
		<currentCall> CurrentCall:K => BackToCall </currentCall>
		<currentComponent> CurrentComponent:Path => BackToComponent </currentComponent>
		<currentVarValues>
			CurrentValuation:Map
			=> 
			copyEntries (
				CurrentValuation ,
				source: (CurrentComponent @ CurrentCall) , SourceInouts ,
				target: (BackToComponent @ BackToCall) , TargetInouts
			)
		</currentVarValues>


	// Note: Behaviour should only be called by other behaviours (and never from provided ports)!!!!!!!!!!!!!

	// (beh)
	rule
		<k> (SubComponentId:Id) ( ) => Stmnt ... </k>
		<currentVarValues>
			CurrentValuation:Map => freshVarEntries (CurrentValuation , (CurrentComponent . SubComponentId ) , Vars )
		</currentVarValues>
		<currentComponent> CurrentComponent:Path => ( CurrentComponent . SubComponentId ) </currentComponent>
		<component>
			<path> ( CurrentComponent . SubComponentId ) </path>
			<behaviour> Vars:TypedVarDeclarations ; Stmnt:Stmnt </behaviour>
			...
		</component>


endmodule


module SAFETYSHARP
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION
	
	// if you just want to know how initialization of all cells works and looks like for a specific program, just comment out the following line
	imports SAFETYSHARP-SEMANTICS

endmodule
