module SAM-SYNTAX
// This is just a simple demo-parser to read programs in SAM. We just
// assign some syntax to define the domains and to describe the semantics.
// Precedence rules makes it easier to write demo-programs. SAM itself is
// syntax-independent.

// Notes:
//	* [left] means left-associative
//	* [strict] means that all terms are evaluated first (in indeterministic order), and then the operator-rule is used
//	* [strict(2] means that the second term is evaluated first. Then the operator-rule is used (common example use-case: lazy evaluation of "Expr && false"; short-circuit-semantics. We use it to emphasize, that to evaluate an assignment-Statement, we first have to evaluate the expression)
//	* [seqstrict] means that all operations with the same precedence have to be evaluated from left to right (deterministic order)
//	* For many details on the see http://www.kframework.org/language-pdfs/new/imp.pdf which shares a lot of common concepts with SAM and has a very detailed documentation.
//	* [transition] is necessary to show k, that a rule leads to non-determinism, which should explored

// Chapter 2.1: Domains
	syntax Var ::= Id
	syntax Value ::= Bool | Int	

// Chapter 2.2: Expressions
	syntax Expr ::=   Var
			| Id
			| Value
			| Expr "/" Expr		[left,strict]
			| Expr "*" Expr		[left,strict]
			| Expr "%" Expr 	[left,strict]
			> Expr "+" Expr		[left,strict]
			| Expr "-" Expr		[left,strict]
			> Expr "<=" Expr	[left,strict]            
			| Expr "==" Expr	[left,strict]
			| Expr "=/=" Expr	[left,strict]
			| Expr "=>" Expr	[left,strict]
			| Expr ">=" Expr	[left,strict]
			| Expr ">" Expr		[left,strict]
			| Expr "<" Expr		[left,strict]
			| "!" Expr                  
			> Expr "&&" Expr	[left,strict] 
			> Expr "||" Expr	[left,strict]
			| "prev" "(" Var ")"
			| "(" Expr ")"		[bracket]
// Chapter 2.3: Statements
	syntax GuardedCommand ::= Expr "=>" "{" StmFils "}" //[strict(1)] //evaluate Guard, but not Statement. Strictness not necessary, because context rule takes care of it
	
	syntax GuardedCommands ::= List{GuardedCommand,""}

	//we need a context to express, that even in a list of GuardedCommands (eg: Guard1:Stmt1 , Guard2:Stmt2, ...), the first Guard should be evaluated (see K-Primer 2012 page 14). Context is similar to strictness
	context (choice { (HOLE => { Stmnt:StmFil }) OtherCandidates:GuardedCommands } )

	syntax StmFil ::= Var ":=" Expr	";"	[strict(2)]
			| "{" StmFils "}"	[bracket]
			| "choice" "{" GuardedCommands "}"

	//[left] //could also be [left,seqstrict], but this is more efficient, because the terms get expanded only when required (see rule (seq)

	syntax StmFils ::= List{StmFil,""}


	syntax K ::= StmFil
	syntax K ::= Expr
	syntax KResult ::= Value // necessary, so K knows, that evaluation of the current calculationi cell cannot go any further, when a Value is in the first calculation cell. K can now put the result of the first calculation cell into the HOLE of the next calculation cell. (Example. Assume term "12 ~> i := HOLE". K knows, that 12 is a result, so K can put 12 into HOLE. So the result is "i := 12".
endmodule

module SAM-CONFIGURATION
	imports SAM-SYNTAX
// Chapter 2.1: Domains, variable environment
	configuration
		<k> $PGM:StmFils </k>
		<varEnvNow> .Map </varEnvNow> //Map from Var to Value. Current Valuation
		<varEnvStep> .Map </varEnvStep> //Map from Var to Value. Valuation from the beginning of the current Step
		<cmdCandidates> .Set </cmdCandidates> //Set of possibilities, which can be taken for the next step of a guarded Command (gc) other name <gcPossibleDecisions>
endmodule

module SAM
	imports SAM-SYNTAX
	imports SAM-CONFIGURATION
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
	//rule '_=>_(I1:Int,,I2:Int) => '>=_Int_(I1,,I2) //to omit parsing ambiguity
	rule I1:Int >= I2:Int => I1 >=Int I2
	rule I1:Int > I2:Int => I1 >Int I2
	rule I1:Int < I2:Int => I1 <Int I2
	rule ! B:Bool => notBool B 
	rule B1:Bool && B2:Bool => B1 andBool B2
	rule B1:Bool == B2:Bool => B1 ==Bool B2
	rule B1:Bool || B2:Bool => B1 orBool B2
	rule B1:Bool =/= B2:Bool => B1 =/=Bool B2
	
	// SAM-specific interpretation of expressions
	rule
		<k> V:Var => Val:Value ... </k>
		<varEnvNow> V |-> Val ... </varEnvNow>

	rule
		<k> prev ( V:Var ) => Val:Value ... </k>
		<varEnvStep> V |-> Val ... </varEnvStep>

	// Chapter 2.3: Statements
	// (skip)
	rule
		<k> .StmFils => .K ... </k>
	
	// (assign)
	// create new Variable in varEnv, if not existent
	rule
		<k> (Var := Val:Value ;) => . ... </k>
		<varEnvNow> AlreadyDeclared:Map (.Map => Var |-> Val) </varEnvNow>
			when notBool (Var in keys(AlreadyDeclared))

	// overwrite Variable in varEnv, if already existent
	rule
		<k> (Var := Val:Value ;) => . ... </k>
		<varEnvNow> Var |-> (OldVar => Val) ...  </varEnvNow>

	// (seq)
	rule
		<k> S:StmFil OtherStmnts:StmFils => S ~> OtherStmnts ... </k>
	

	// (cmd)
	// 4 Steps to evaluate a GuardedCommand
	//   * 1)  evaluate the guard of the first GuardedCommand in the current Cell (done by [strict(1)])
	//   * 2a) if this guard is false, throw away the first GuardedCommand
	//   * 2b) if this guard is true, put the Command into the list of gcCurrentCandidates
	//   * 3) Repeat until all GuardedCommands are evaluated
	//   * 4)  When every GuardedCommand is evaluated, the current k-Cell contains .GuardedCommands. Now replace .GuardedCommands with any candidate from the list and delete all candidates

	rule
		<k> (choice { (false => { Stmts:StmFils } ) OtherCandidates:GuardedCommands => OtherCandidates } ) ... </k>

	rule
		<k> (choice { (true => { Stmts:StmFils } ) OtherCandidates:GuardedCommands => OtherCandidates } ) ... </k>
		<cmdCandidates> (.Set => SetItem(Stmts) ) OtherSuccessfulCandidates:Set </cmdCandidates>
	
	rule
		<k> (choice { .GuardedCommands } => Stmts) ... </k>		//Alternative way to express (may become handy): <k> (.GuardedCommands => Stmt) ~> OtherCalculations:K </k>
		<cmdCandidates> (SetItem(Stmts) => .Set ) (OtherSuccessfulCandidates:Set => .Set) </cmdCandidates> [transition]

endmodule
