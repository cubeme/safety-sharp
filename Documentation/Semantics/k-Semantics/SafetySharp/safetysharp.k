// SafetySharp uses a lot of FIL. For information how [strict], context, [left], [strict(2)], and [transition] works, see fil.k

// The semantics document describes a semantics, which is sometimes typed explicitly and sometimes not. For now, this k-Semantics is as a whole not typed explicitly.

module SAFETYSHARP-SYNTAX
// Chapter 2.1: Domains
	syntax LocalVar ::= Id
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
	syntax GuardedCommand ::= Expr "->>" "{" StmFil "}"
	
	syntax GuardedCommands ::= List{GuardedCommand,","}

	context ((HOLE ->> { Stmnt:StmFil }), OtherCandidates:GuardedCommands)

	syntax StmFil ::= "skip"
			| LocalVar ":=" Expr	[strict(2)]
			| StmFil ";" StmFil	[left]
			| GuardedCommands

	syntax LocalVarDecl ::= List{LocalVar, ","}
	syntax MiniProgram ::= LocalVarDecl ";" StmFil

	syntax K ::= StmFil
	syntax K ::= Expr
	syntax KResult ::= Value 

// Chapter 3: Component Structure
	// First step is to parse the Component Structure and write its content into the corresponding k-Cells. Most of the syntactic stuff here is only necessary to for this first step and not necessary to describe the details of the semantics. But it cannot be extracted into an own module, because if "syntax Component" is not defined in "module SAFETYSHARP-SYNTAX" (or whatever is defined as syntax-module with "kompile --syntax-module"  it cannot be used in the configuration.
	// TODO: for now I ignore the distinction in the syntax between Declarations and Instantiantions and leave out Types
	
	syntax Component ::= "component" Id "{" Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour "}" // Chapter 3.1.6
//	syntax Component ::= "component" Id //"{" "}"	

	syntax Field ::= Id "=" Values
	syntax RequiredPort ::= Id "r(" IdList ";" IdList ")" //actually the names are not important, just the number of parameters. Actually, if Id is unique, even their number is not important.
	syntax ProvidedPort ::= Id "p(" IdList ";" IdList ")" "{" MiniProgram "}"
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
	syntax IdList ::= List{Id,","}

	syntax HierarchicalAccess ::=	  Id 
					| HierarchicalAccess "." Id		[left]
	syntax K ::= Component
endmodule

module SAFETYSHARP-CONFIGURATION
	imports SAFETYSHARP-SYNTAX

	syntax LoadComponent ::= "#loadRootComponent" "(" Component ")"

	syntax LoadComponent ::= "#loadComponent" "(" Component "," HierarchicalAccess "," Set ")" //second argument is the full Path of the component to load, third argument are the HierarchicalAccesss' of previously loaded Subcomponents of Component
	// Chapter 2.1: Domains, variable environment
	syntax K ::= LoadComponent


	configuration
		<execution>
			<loadComponents multiplicity="?"> #loadRootComponent ( $PGM:Component ) </loadComponents>
			<k> .K  </k>
			<gcCurrentCandidates> .Set </gcCurrentCandidates> //Set of possibilities, which can be taken for the next step of a guarded Command (gc)
			<currentFieldValues> .Map </currentFieldValues>  // (<path>:HierarchicalAccess).FieldName |-> Value
		</execution>
		<static>
			<component multiplicity="*">
				<path> .K </path> // Type should be HierarchicalAccess. Example n1.n2.n3... where n1=parent(n2), root=n1, n2=parent(n3), 
				<subcomponents> .Set </subcomponents> //Set of paths of subcomponents
				<requiredPort> .Set </requiredPort>
				<providedPort> .Set </providedPort>
				<bindings> .Map </bindings>
				<behaviour> .K </behaviour>
				<fields> .List </fields>
			</component>
		</static>




	rule
		<loadComponents>
			#loadRootComponent ( component ComponentName:Id { Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } )
			=>
			#loadComponent ( component ComponentName:Id { Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , ComponentName , .Set ) ... </loadComponents>
	
	// loadComponents initially contains the main component, with the following structural rules, we load the components in their corresponding cells in <static> and initialize the main behavior
	rule
		<loadComponents> #loadComponent ( component ComponentName:Id { .Components Fields RequiredPorts ProvidedPorts Bindings ComponentBehaviour } , FullPath:HierarchicalAccess , SubComponents:Set ) => .K ... </loadComponents>
		<static>
			. =>
			<component>
				<path> FullPath </path> //use quoted notation to omit parsing ambiguities
				<subcomponents> SubComponents </subcomponents> 
				<requiredPort> .Set </requiredPort>
				<providedPort> .Set </providedPort>
				<bindings> .Map </bindings>
				<behaviour> .K </behaviour>
				<fields> .List </fields>
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


endmodule

module SAFETYSHARP
	imports SAFETYSHARP-SYNTAX
	imports SAFETYSHARP-CONFIGURATION

/*
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
	
	// FIL-specific interpretation of expressions
	rule
		<k> V:Var => Val:Value ... </k>
		<varEnvNow> V |-> Val ... </varEnvNow>

	// Chapter 2.3: Statements
	// (skip)
	rule
		<k> skip => . ... </k>
	
	// (assign)
	// create new Variable in varEnv, if not existent
	rule
		<k> (Var := Val:Value) => . ... </k>
		<varEnvNow> AlreadyDeclared:Map (.Map => Var |-> Val) </varEnvNow>
			when notBool (Var in keys(AlreadyDeclared))

	// overwrite Variable in varEnv, if already existent
	rule
		<k> (Var := Val:Value) => . ... </k>
		<varEnvNow> Var |-> (OldVar => Val) ...  </varEnvNow>

	// (seq)
	rule S1:StmFil ; S2:StmFil => S1 ~> S2
	

	// (cmd)
	// 4 Steps to evaluate a GuardedCommand
	//   * 1)  evaluate the guard of the first GuardedCommand in the current Cell (done by [strict(1)])
	//   * 2a) if this guard is false, throw away the first GuardedCommand
	//   * 2b) if this guard is true, put the Command into the list of gcCurrentCandidates
	//   * 3) Repeat until all GuardedCommands are evaluated
	//   * 4)  When every GuardedCommand is evaluated, the current k-Cell contains .GuardedCommands. Now replace .GuardedCommands with any candidate from the list and delete all candidates

	rule
		<k> ((false ->> { Stmt:StmFil } ) , OtherCandidates:GuardedCommands) => OtherCandidates  ... </k>

	rule
		<k> ((true ->> { Stmt:StmFil } ) , OtherCandidates:GuardedCommands) => OtherCandidates  ... </k>
		<gcCurrentCandidates> (.Set => SetItem(Stmt) ) OtherSuccessfulCandidates:Set </gcCurrentCandidates>
	
	rule
		<k> (.GuardedCommands => Stmt) ... </k>		//Alternative way to express (may become handy): <k> (.GuardedCommands => Stmt) ~> OtherCalculations:K </k>
		<gcCurrentCandidates> (SetItem(Stmt) => .Set ) (OtherSuccessfulCandidates:Set => .Set) </gcCurrentCandidates> [transition]
*/
endmodule
