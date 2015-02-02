// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Analysis.SmtSolving.Z3.Ast

// Here we add some of Z3's Datastructures, which extend SMT-LIBv2

// http://rise4fun.com/z3/tutorial/guide
// http://rise4fun.com/Z3/tutorial/fixedpoints
// http://rise4fun.com/Z3/tutorial/strategies http://rise4fun.com/z3/tutorialcontent/strategies
// http://research.microsoft.com/en-us/um/redmond/projects/z3/class_microsoft_1_1_z3_1_1_goal.html#details
// http://research.microsoft.com/en-us/um/people/leonardo/strategy.pdf

// reverse engineered from "display"-functions and other output-functions in the source files
// Source-File: z3/src/cmd_context/tactic_cmds.cmd     <-- input of z3
// Source-File: z3/src/cmd_context/simplify_cmds.cmd   <-- input of z3
// Source-File: z3/src/api/api_tactic.cpp              <-- output of "goals"
// Source-File: z3/src/tactic/goal.cpp                 <-- output of ":precision" and "(goal"
// Source-File: z3/src/ast/ast.h                       <-- declaration of expr
// Source-File: z3/src/ast/ast_smt2_pp.cpp             <-- output of Expression

open SafetySharp.Analysis.SmtSolving.SmtLib2.Ast

// TODO: Custom einführen (hier und in SMTLIBv2). Damit kann ein reguläres Ding hier in ein Custom da überführt werden und umgekehrt. Vielleicht ein Custom SMT-Interface genierieren, was eine toString-Methode enthalten soll
// TODO: Analyse dotnet api
// TODO: Input-Commands

// Precision (goal.cpp line 32 / goal.h line 41)
type internal Precision = PrecisionPrecise | PrecisionUnder | PrecisionOver | PrecisionUnderOver

// depth of the goal in the goal tree (goal.h line 57)
type internal Depth = int

// Expr is the "Superclass for applications, variables and quantifiers" (ast.h line 603)
// This can be mapped to SMT-LIBv2 with Term
// The output in Z3 is done with "ast/ast_smt2_pp.cpp" as Expr inherits from Ast in Z3
type internal Expr = Term
// TODO (incomplete): GoalDependency contains for every Expr in Goals its dependencies and the definitions (display_with_dependencies in goal.cpp)
type internal GoalDependencyEntry =
    | GoalDependencyEntryEntryInDefinitionTable of key:string
    | GoalDependencyEntryConstant of cons:string
type internal GoalDependency = {exprDependency : Map<Expr,GoalDependencyEntry list>;  dependencyDefinitions : Map<string,Expr>}
// A goal is a list of formulas (expr), a precision and a depth (display-function in goal.cpp line 300)
type internal Goal = Expr list * Precision * Depth * GoalDependency option



// Output of Z3
// Goals is a list of 0..* subgoals (api_tactic.cpp line. 471)
type internal Goals = Goal list


// apply-Command und Tactics

// Input of Z3
type internal Tactics =
    | TacticsSkip
    | TacticsSolveEqs
    | TacticsSplitClause
    | TacticsSimplify
    | TacticsCtxSolverSimplify
    | TacticsAig // tries to compress Boolean formulas
    | TacticsNormalizeBounds
    //| TacticsFailIf of Condition
    //| TacticsEcho of ...
    //... TODO: many more. See (help-tactic)


// Input of Z3
// Tutorial talks in the description of tacticals of "the given tactic" even if in the later examples a tactical is used instead of a tactic 
type internal Parameter = {Keyword : string; Value:string}


// Input of Z3
type internal Tacticals =
    | TacticalsTactics of Tactics
    | TacticalsThen of Tacticals list
    | TacticalsParThen of Tacticals list
    | TacticalsOrElse of Tacticals list
    | TacticalsIfThenElse of cond:Tacticals * thenBranch:Tacticals * elseBranch:Tacticals
    | TacticalsWhen of cond:Tacticals * thenBranch:Tacticals
    | TacticalsParOr of Tacticals list
    | TacticalsRepeat of Tacticals
    | TacticalsRepeatUntilN of Tacticals * maxIterations:int
    | TacticalsTryForTime of Tacticals * maxTimeInMs:int
    | TacticalsUsingParameter of Tacticals * (Parameter list) //TODO: ist dies für Tactics oder für Tacticals

// Best thing to do to understand the following is to read Chapter "Datatypes" of "Z3 - Guide" available on http://rise4fun.com/Z3/tutorial/guide
type internal AccessorDecl = {accessPartialContentFunctionName:Symbol; typeOfPartialContent: Sort} //PartialContent, because there may be more AccessorDecls in one Constructor

type internal ConstructorDecl = {constructorName:Symbol; content:AccessorDecl list}

type internal DatatypeDeclaration = {nameOfDatatype:Symbol; constructors:ConstructorDecl list}

type internal DeclareDataTypes = {formalParameters:Symbol list; datatypes:DatatypeDeclaration list} // A declaration may contain more Datatypes, because they might be mutually recursive

// TODO:
// What is the difference between "CommandDefineSort" of SMTLIB2 and "CommandZ3DeclareDatatypes" of Z3?
// TODO: Maybe in Z3 QualIdentifier is equivalent to Symbol in SMTLIB
// CommandZ3DeclareDatatypes of Symbol list * (Symbol * (Symbol * (SortedVar) list) list) list
// CommandDeclareSort        of name:Symbol * numberOfParameters:Numeral


// Input of Z3
// To get more information, use "(help)" in the Z3-Shell
type internal CommandZ3 =
    | CommandZ3Apply of Tacticals * (Parameter list)
    | CommandZ3CheckSatUsing of Tacticals * (Parameter list)
    | CommandZ3GetModel
    | CommandZ3DeclareConst of SortedVar //Could be replaced in SMTLIB2 by a function without an argument
    | CommandZ3DeclareDatatypes of DeclareDataTypes
    | CommandZ3Reset
    | CommandZ3Simplify //Could also be done with the application of TacticsSimplify. TacticsCtxSolverSimplify is more expensive but also more pwerful
    with interface ICommand

(*
 (declare-datatypes (<symbol>* ) (<datatype-declaration>+))
    declare mutually recursive datatypes.
    <datatype-declaration> ::= (<symbol> <constructor-decl>+)
    <constructor-decl> ::= (<symbol> <accessor-decl>* )
    <accessor-decl> ::= (<symbol> <sort>)
    example: (declare-datatypes (T) ((BinTree (leaf (value T)) (node (left BinTree) (right BinTree)))))
*)
(*
(declare-const <symbol> <sort>)
   declare a new constant.
*)

// Simplify

// Outcome of Simplification and other Tactics can be "satisfiable (i.e., feasible); succeeds in showing G to be unsatisfiable (i.e., infeasible); produces a sequence of subgoals; or fails"
