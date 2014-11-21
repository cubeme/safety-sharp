// Notes:
// 	* SafetySharp uses a lot of FIL. For information how [strict], context, [left], [strict(2)], and [transition] works, see fil.k
//	* "'A`(_;_`)(Parameter1,,Parameter2)" is another form to write down "A(Parameter1;Parameter2)" to omit parsing ambiguities. To escape '(' we write '`)'. To escape '{' we write '`{'
//	* Alternative way to express "(.GuardedCommands => Stmt) ..." is "(.GuardedCommands => Stmt) ~> OtherCalculations:K"
//	* Starting with k-Framework release 3.4.1 (not officially released yet), the map operations could be expressed more concisely
//	* When two different cells are written down (in his example two times <component>), k assumes, that these _are_ actually different cells, so we have to write a rule for the case, when it is actually one cell
//	* The semantics document describes a semantics, which is sometimes typed explicitly and sometimes not. For now, this k-Semantics is as a whole not typed explicitly.
////	* Be careful: when two comma-separated expressions are in the first k-Cell,
//	  k might mistake it for a ExprList, where the first term before the comma needs
//	  to be evaluated (because of the [strict]. Thus ensure, that comma-separated
//	  values occur in the first k-Cell only when they need to be evaluated.
//	  We use the [strict] to evaluate the inputs of a required-port. An alternative
//	  would be to declare a better "context"-rule
//	  That is the reason, we could not use "," as separator in guarded commands.
//	  It lead to a HOLE, which stopped the interpretation in example "cmd1.safetysharp"
//	  "<k> true ->> { fieldInt := 20 } ~> HOLE, (6 > 4) ->> { fieldInt := 30 }, ..."
//	  A context rule might look like this (incomplete)
//		context Id:Id ( HOLE , OtherExpr:ExprList ; IdList )
//		context Id:Id ( Value:KResult , (HOLE, OtherExpr:ExprList) ; IdList )
//	  Recall: "HOLE designates the position to be evaluated first" (k-primer 2012 p.14)

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
	
	syntax GuardedCommands ::= List{GuardedCommand,"|||"}

	context ((HOLE ->> { Stmnt:Stmnt }) ||| OtherCandidates:GuardedCommands)

	syntax Stmnt ::= "skip"			// do nothing
			| Id ":=" Expr	[strict(2)]	// assignment to Variable or Field
			| Stmnt ";" Stmnt	[left]	// Sequential Composition
			| GuardedCommands		// Guarded Commands (generalized if-then-else; see wikipedia http://en.wikipedia.org/wiki/Guarded_Command_Language)
			| Id "(" ExprList ";" IdList ")"	[strict(2)] // Call a required port or a provided port, expressions should be evaluated first
			| Id "(" ")"			// Call behaviour of sub-component

	syntax ExprList ::= List{Expr,","}	[strict]	//List of expressions should be evaluated automatically, when a list like this appears in the first k-Cell. Todo: Rename to Exprs to remain consistent
	
	syntax MiniProgram ::= TypedVarDeclarations "." Stmnt

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
	
	syntax LoadComponent ::= "#createInitialExecutionContext"

	syntax K ::= LoadComponent

	//TODO: Find better place	
	syntax K ::= "#chooseInitialValue" "(" Path "," Id ")" //for a specific Field. FullPath to Component, FieldId

	configuration
		<loadComponents multiplicity="?"> #createInitialExecutionContext ~> #loadRootComponent ( $PGM:Component ) </loadComponents>
		<execution multiplicity="*">
			<executionContextId> 0 </executionContextId>
			// The corresponding elements to the Configuration of Chapter 3.3 in the semantics document are written in "[~= _ ]"			
			<k> .K  </k>	// [~= S \in Stm_{fm}]  (plus initialisation of fields)
			<currentFieldValues> .Map </currentFieldValues>  // (<path>:Path).FieldName |-> Value. [~= \phi \in \Phi]
			<currentVarValues> .Map </currentVarValues> // (VarName |-> Value (without hierarchie).  [~= \varsigma \in \Sigma_{fm}]
			<currentComponent> .K </currentComponent> // Path to current component (Path) [~= c^+]
			<cmdCandidates> .Set </cmdCandidates> //Set of possibilities, which can be taken for the next step of a guarded Command (gc)
		</execution>
		<nextFreeContext>1</nextFreeContext>
		<static>
			// Extracting the bindings from the component-hierarchy makes the semantics easier to read. Formerly, when bindings had their cell in the bindings, there were several restrictions, where bindings in the source file could be declared. Also it shrank down the number of rules to call a required port. Now we only need to differentiate between two cases (required port in the same component vs. in a different component) for delayed ports. E.g. it was not that easy to connect in component c1 the required port p1 of c1.c2 to provided port p2 of c1.c2.
			// And it also fits to the idea that components are declared independent from bindings and bindings are "injected" afterwards.
			<instantBindings> .Map </instantBindings>	// component1:Path . to_required:Id |-> component2:Path . from_provided:Id
			<delayedBindings> .Map </delayedBindings>	// component1:Path . to_required:Id |-> component2:Path . from_provided:Id
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
				<field multiplicity="*">
					<fiIdentifier> .K </fiIdentifier>
					<fiPossibleValues> .Values </fiPossibleValues>
				</field>
				<behaviour> .K </behaviour>
			</component>
		</static>


	rule
		<loadComponents> #createInitialExecutionContext => . ... </loadComponents>
		(.
		=>
		<execution>
			<executionContextId> 0 </executionContextId>			
			<k> .K  </k>
			<currentFieldValues> .Map </currentFieldValues>
			<currentVarValues> .Map </currentVarValues>
			<currentComponent> .K </currentComponent>
			<cmdCandidates> .Set </cmdCandidates>
		</execution>)

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
		<execution>
			<executionContextId> 0 </executionContextId>
			<k>
				.K => #chooseInitialValue( FullPath, FieldId ) ...
			</k>
			...
		</execution>	[structural]

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
			<behaviour> LocalVars:TypedVarDeclarations . Code:Stmnt </behaviour>
			...
		</component>
		<execution>
			<executionContextId> 0 </executionContextId>
			<currentComponent> .K => Component </currentComponent>
			<currentVarValues> .Map => freshVarEntries ( target: .Map , LocalVars ) </currentVarValues>
			<k> (.K => Code ) </k>
			...
		</execution>	[structural]
		

endmodule

module SAFETYSHARP-SEMANTICS-CONVENIENCE
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION	

	// use of anyValueOf may lead to indeterminism
	syntax Value ::= "anyValueOf" "(" Values ")" [function]
	rule anyValueOf ( Element1:Value Element2:Value Rest:Values ) => anyValueOf ( Element2 Rest)	[transition]
	rule anyValueOf ( Element:Value Rest:Values) => Element	[transition]


	syntax Map ::= "freshVarEntries" "(" "target:" Map "," TypedVarDeclarations ")"	[function] //Map to delete entries from; Variables to delete

	rule freshVarEntries ( target: ( .Map => Var |-> #missingElement ) FieldMap:Map , ( (Var:Id : Type:Type) , OtherParameter:TypedVarDeclarations => OtherParameter))	when notBool (Var in keys(FieldMap)) 
	rule freshVarEntries ( target: FieldMap:Map , .TypedVarDeclarations ) => FieldMap
		
	syntax Map ::= "copyEntries" "("
				"source:" Map "," IdList ","	//SourceMap:Map
				"target:" Map "," IdList ")"	[function] //TargetMap:Map

	rule copyEntries (	source: (FromId |-> NewValue:Value)  FromFieldMap:Map ,
				(FromId:Id , OtherFroms => OtherFroms),
				target: (ToId |-> (OldValue => NewValue)) ToFieldMap:Map ,
				(ToId:Id , OtherTos => OtherTos))

	rule copyEntries (	source: (FromId |-> NewValue:Value)  FromFieldMap:Map ,
				(FromId:Id , OtherFroms => OtherFroms),
				target: (. => (ToId |-> NewValue)) ToFieldMap:Map ,
				(ToId:Id , OtherTos => OtherTos))	when notBool (ToId in keys(ToFieldMap)) 
	rule copyEntries (	source:  FromFieldMap:Map , .IdList ,
				target:  ToFieldMap:Map , .IdList ) => ToFieldMap


	syntax Map ::= "assignValues" "("
				"values:" ExprList "," // ExprList should be already evaluated Expressions (thus a list of Values)
				"target:" Map "," IdList ")"	[function] //TargetMap:Map

	rule assignValues (	values:  (( Value:Value , OtherExprs:ExprList ) => OtherExprs),
				target:  ( Var |-> (OldValue => Value) ) FieldMap:Map,
				(Var:Id  , OtherVars:IdList => OtherVars ) )

	rule assignValues (	values:  (( Value:Value , OtherExprs:ExprList ) => OtherExprs),
				target:  ( .Map =>  Var |-> Value ) FieldMap:Map,
				(Var:Id  , OtherVars:IdList => OtherVars ) )	when notBool (Var in keys(FieldMap))

	rule assignValues (	values:  .ExprList ,
				target:  FieldMap:Map ,
				.IdList ) => FieldMap


	syntax IdList ::= "extractIds" "(" TypedVarDeclarations ")" [function]

	rule extractIds ( ( Id:Id : Type:Type ) , OtherVars:TypedVarDeclarations) => (Id , extractIds ( OtherVars ) )

	rule extractIds ( .TypedVarDeclarations ) => .IdList

	
	// @ is used in initialization and for (beh) and (call)
	// only use @ on the right side of a rewrite rule (=>). On the left it isn't evaluated
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
		<execution>		
			<k>			
				#chooseInitialValue( FullPath:Path, FieldId:Id ) => . ...
			</k>
			<currentFieldValues>
				.Map => (FullPath . FieldId) |-> anyValueOf(PossibleValues) ...
			</currentFieldValues>
			...
		</execution>
		<component>
			<path> FullPath </path>
			<field>
				<fiIdentifier> FieldId </fiIdentifier>
				<fiPossibleValues> PossibleValues </fiPossibleValues>...
			</field>
			...
		</component>


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
		<execution>
			<k> Var:Id => Val ... </k>
			<currentVarValues> (Var |-> Val:Value) ... </currentVarValues>
			...
		</execution>



	// Expressions: field access
	rule
		<execution>
			<k> Field:Id => Val ... </k>
			<currentFieldValues>  ((CurrentComponent . Field) |-> Val:Value) ... </currentFieldValues>
			<currentComponent> CurrentComponent:Path </currentComponent>
			...
		</execution>


	// (skip)
	rule
		<execution>
			<k> skip => . ... </k>
			...
		</execution>
	

	// (assign local variable)
	rule
		<execution>
			<k> (Var:Id := Val:Value) => . ... </k>
			<currentVarValues> ( Var |-> (OldVal:Value => Val)) ...</currentVarValues>
			...
		</execution>

	// (assign field)
	rule
		<execution>
			<k> (Field:Id := Val:Value) => . ... </k>
			<currentFieldValues> ( (CurrentComponent . Field) |-> (OldVal:Value => Val)) ... </currentFieldValues>
			<currentComponent> CurrentComponent:Path </currentComponent>
			...
		</execution>

	// (seq)
	rule
		<execution>
			<k> S1:Stmnt ; S2:Stmnt => S1 ~> S2 ... </k>
			...
		</execution>
	

	// (cmd)
	// 4 Steps to evaluate a GuardedCommand
	//   * 1)  evaluate the guard of the first GuardedCommand in the current Cell (done by [strict(1)])
	//   * 2a) if this guard is false, throw away the first GuardedCommand
	//   * 2b) if this guard is true, put the Command into the list of cmdCandidates
	//   * 3) Repeat until all GuardedCommands are evaluated
	//   * 4)  When every GuardedCommand is evaluated, the current k-Cell contains .GuardedCommands. Now replace .GuardedCommands with any candidate from the list and delete all candidates
	rule
		<k> ((false ->> { Stmt:Stmnt } ) ||| OtherCandidates:GuardedCommands) => OtherCandidates  ... </k>

	rule
		<execution>
			<k>
				((true ->> { Stmt:Stmnt } ) ||| OtherCandidates:GuardedCommands) => OtherCandidates  ...
			</k>
			<cmdCandidates>
				(.Set => SetItem(Stmt) ) OtherSuccessfulCandidates:Set
			</cmdCandidates>
			...
		</execution>
	
	rule
		<execution>
			<k> (.GuardedCommands => Stmt) ... </k>
			<cmdCandidates> (SetItem(Stmt) => .Set ) (OtherSuccessfulCandidates:Set => .Set) </cmdCandidates>
			...
		</execution> [transition]

	// (call) and (beh)
	// In this file we implemented way 1
	
	// TODO: If a delayed binding gets called more times? Need to keep track of the execution call -> add to configuration
	
	// Bindings are done in a slightly different way compared to the semantics document.
	// Here we use the current component always as reference

	// We ensure on the call of a behaviour or a port, that all variables which might be accessed are "fresh"

	// explain (beh) first, because it is easier to comprehend and (call) contains parts of its thoughts

	// Note: Behaviour should only be called by other behaviours (and never from provided ports)!!!!!!!!!!!!!
	// TODO: Pop back stack
	// (beh)
	syntax K ::= "#continueWithResult" "(" "contextId:" Int ")"

	rule
		<execution>
			<executionContextId> Origin:Int </executionContextId>
			<k>
				(SubComponentId:Id) ( )
				=>
				#continueWithResult ( contextId: FreeContext)
				...
			</k>
			<currentFieldValues> CurrentFieldValues:Map </currentFieldValues>
			<currentVarValues> CurrentValuation:Map	</currentVarValues>
			<currentComponent> CurrentComponent:Path </currentComponent>
			...		
		</execution>
		<nextFreeContext>FreeContext:Int => FreeContext +Int 1</nextFreeContext>
		(.=> <execution>
			<executionContextId> FreeContext </executionContextId>			
			<k> Stmnt  </k>
			<currentFieldValues> CurrentFieldValues </currentFieldValues>
			<currentVarValues> freshVarEntries ( target: .Map, Vars) </currentVarValues>
			<currentComponent> CurrentComponent . SubComponentId </currentComponent>
			<cmdCandidates> .Set </cmdCandidates>
		</execution>)
		<component>
			<path> ( CurrentComponent . SubComponentId ) </path>
			<behaviour> Vars:TypedVarDeclarations . Stmnt:Stmnt </behaviour>
			...
		</component>

	// (beh (part write-back))
	// Note: The context is different from the context of
	rule		
		<execution>
			<k> #continueWithResult ( contextId: NewContext:Int) => .K ... </k>
			<currentFieldValues> OldFieldValues:Map => NewFieldValues </currentFieldValues>
			...
		</execution>
		(<execution>
			<executionContextId> NewContext </executionContextId>			
			<k> .K </k>	// Cell was processed completely
			<currentFieldValues> NewFieldValues:Map </currentFieldValues>
			...
		</execution> => .)



	// (call)
	// This is a call of a Required Port. Provided Ports cannot be called (according to the full semantics)
	// We split up the call into two rules. TODO: describe
	// Because we applied the [strict] rules on the call-Statment and the ExprList, the Inputs are already evaluated, when this Statement appears in the first k-Cell
	syntax K ::= "#continueWithResultAndCopyVariables" "(" 
			"contextId:" Int "," IdList "," // ContextToCopyFrom:Int SourceInouts:TypedVarDeclarations
			"to:" IdList ")" // TargetInouts:TypedVarDeclarations

	// (call instantaneous)
	//	* RequiredPortComponent = ProvidedPortComponent (= CurrentComponent)
	// 	* parent(RequiredPortComponent) = ProvidedPortComponent)
	// 	* parent(RequiredPortComponent) = parent(ProvidedPortComponent; RequiredPortComponent!=ProvidedPortComponent)
	// 	* RequiredPortComponent = parent(ProvidedPortComponent)
	// CurrentComponent = RequiredPortContext
	// could be called in a behaviour or in a provided port
	// Context depends on Component and Call
	rule
		<execution>
			<k> 
				(RequiredPortName:Id ( InputValues:ExprList ; InoutsOfCurrentContext:IdList ))				=>
				#continueWithResultAndCopyVariables (
					contextId: FreeContext , extractIds(InoutsOfNextContext) ,
					to:   InoutsOfCurrentContext)
				...
			</k>
			<currentComponent> CurrentComponent:Path </currentComponent>
			<currentFieldValues> CurrentFieldValues:Map </currentFieldValues>
			<currentVarValues> CurrentValuation:Map	</currentVarValues>
			...
		</execution>
		<instantBindings> ( (CurrentComponent . RequiredPortName) |-> (ProvidedPortComponent:Path . ProvidedPortName:Id ) ) OtherBindings:Map </instantBindings>
		<component>
			<path> ProvidedPortComponent </path>
			<providedPort multiplicity="*">
				<ppIdentifier> ProvidedPortName </ppIdentifier>
				<ppInputs> PpInputs:TypedVarDeclarations </ppInputs>
				<ppInouts> InoutsOfNextContext:TypedVarDeclarations </ppInouts>
				<ppCode> LocalVars:TypedVarDeclarations . CodeOfProvidedPort:Stmnt </ppCode>
			</providedPort>
			...
		</component>
		<nextFreeContext>FreeContext:Int => FreeContext +Int 1</nextFreeContext>
		(.=> <execution>
			<executionContextId> FreeContext </executionContextId>			
			<k> CodeOfProvidedPort  </k>
			<currentFieldValues> CurrentFieldValues </currentFieldValues>
			<currentVarValues>
				// first copy inputs and inouts, then set every local entry to the #missingElement
				freshVarEntries(					
					target: copyEntries( //inouts
							source: CurrentValuation , InoutsOfCurrentContext ,
							target: assignValues (	//inputs
									values: InputValues , // InputValues have already been evaluated (because we declared the call-expression as strict)
									target: .Map , extractIds(PpInputs))	
							, extractIds(InoutsOfNextContext)
						)
					,
					LocalVars )
			</currentVarValues>
			<currentComponent> ProvidedPortComponent </currentComponent>
			<cmdCandidates> .Set </cmdCandidates>
		</execution>)

	// (call (part write-back))
	// Note: The context is different from the context of
	rule
		<execution>
			<k> #continueWithResultAndCopyVariables (
					contextId: NewContext:Int , SourceInouts:IdList ,
					to:   TargetInouts:IdList) => .K ... </k>
			<currentFieldValues> OldFieldValues:Map => NewFieldValues </currentFieldValues>
			<currentVarValues>
				OldVarValues:Map
				=> 
				copyEntries (
					source: NewVarValues , SourceInouts ,
					target: OldVarValues , TargetInouts
				)
			</currentVarValues>
		...
		</execution>
		(<execution>
			<executionContextId> NewContext </executionContextId>			
			<k> .K </k>	// Cell was processed completely
			<currentFieldValues> NewFieldValues:Map </currentFieldValues>
			<currentVarValues> NewVarValues:Map </currentVarValues>
			...
		</execution> => .)

	// (call delayed)

endmodule


module SAFETYSHARP
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION
	
	// if you just want to know how initialization of all cells works and looks like for a specific program, just comment out the following line
	imports SAFETYSHARP-SEMANTICS

endmodule
