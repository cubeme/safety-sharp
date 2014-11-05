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

module Z3ExamplesFiles


open SMTLIB2DataStructures.Ast
open Z3DataStructures.Ast
open Z3DataStructures.Predefined
open SMTLIB2Convenience

let exampleOutputEmptyGoalString =
    "(goal\n  :precision precise :depth 4)"
let exampleOutputEmptyGoalAst : Goal =
    ([],Precision.PrecisionPrecise,4,None)

let exampleOutputEmptyGoalsString =
    "(goals\n(goal\n  :precision precise :depth 4)\n)"
let exampleOutputEmptyGoalsAst : Goals =
    [exampleOutputEmptyGoalAst]
        
let exampleOutputFileSimplify1aString =
    "(or (= s ON) (= s OFF) (= s BROKEN))\n(and (not (<= a 0)) (not (<= a 1)))"
//let exampleOutputFileSimplify1aAst =
//    Expr.
    
let exampleOutputFileSimplify1bString =
    "(goals\n(goal\n  (not (<= a 1))\n  :precision precise :depth 1)\n)"
let exampleOutputFileSimplify1bAst : Goal list=
    let exprlist = [Expr.TermQualIdTerm(QualifiedIdentifierFromString "not",[ Expr.TermQualIdTerm(QualifiedIdentifierFromString "<=",[Term.TermQualIdentifier(QualifiedIdentifierFromString "a");
                                                                                                                                      Term.TermSpecConstant(SpecConstant.SpecConstantNumeral(bigint(1)))
                                                                                                                                     ])
                                                                            ])
                   ]
    let precision = Precision.PrecisionPrecise
    let depth = 1
    let goaldependency = None
    [exprlist,precision,depth,goaldependency]

let exampleOutputFileSimplify2String =
    "(goals\n(goal\n  (>= t 0)\n  (<= t 1)\n  :precision precise :depth 3)\n)"

let exampleOutputFileTacticsandgoals1String =
    "(goals\n(goal\n  (not (<= y (- 2.0)))\n  (not (<= y 0.0))\n  :precision precise :depth 2)\n)"

let exampleOutputFileUnsat =
    "unsat"


let exampleFileSimplify1bAst : ICommand list=
    [ CommandZ3.CommandZ3DeclareDatatypes {DeclareDataTypes.formalParameters=[];
                                           DeclareDataTypes.datatypes=[{DatatypeDeclaration.nameOfDatatype=Symbol.Symbol("SE");
                                                                        DatatypeDeclaration.constructors=[{ConstructorDecl.constructorName=Symbol.Symbol("BROKEN");ConstructorDecl.content=[]};
                                                                                                          {ConstructorDecl.constructorName=Symbol.Symbol("ON");ConstructorDecl.content=[]};
                                                                                                          {ConstructorDecl.constructorName=Symbol.Symbol("OFF");ConstructorDecl.content=[]}
                                                                                                         ]
                                                                       }
                                                                      ]
                                          };
      CommandZ3.CommandZ3DeclareConst (Symbol.Symbol("s"),SortFromString "SE" );
      CommandZ3.CommandZ3DeclareConst (Symbol.Symbol("a"),SortFromString "Int" );
      Command.CommandAssert (Term.TermQualIdTerm(QualifiedIdentifierFromString "or",[Term.TermQualIdTerm(QualifiedIdentifierFromString "=",[Term.TermQualIdentifier(QualifiedIdentifierFromString "s");Term.TermQualIdentifier(QualifiedIdentifierFromString "ON")]);
                                                                                     Term.TermQualIdTerm(QualifiedIdentifierFromString "=",[Term.TermQualIdentifier(QualifiedIdentifierFromString "s");Term.TermQualIdentifier(QualifiedIdentifierFromString "OFF")]);
                                                                                     Term.TermQualIdTerm(QualifiedIdentifierFromString "=",[Term.TermQualIdentifier(QualifiedIdentifierFromString "s");Term.TermQualIdentifier(QualifiedIdentifierFromString "BROKEN")])
                                                                                    ]));
      Command.CommandAssert (Term.TermQualIdTerm(QualifiedIdentifierFromString "and",[Term.TermQualIdTerm(QualifiedIdentifierFromString ">",[Term.TermQualIdentifier(QualifiedIdentifierFromString "a");Term.TermSpecConstant(SpecConstant.SpecConstantNumeral(bigint(0)))]);
                                                                                      Term.TermQualIdTerm(QualifiedIdentifierFromString ">",[Term.TermQualIdentifier(QualifiedIdentifierFromString "a");Term.TermSpecConstant(SpecConstant.SpecConstantNumeral(bigint(1)))])
                                                                                     ]));
      CommandZ3.CommandZ3Apply(Tacticals.TacticalsTactics(Tactics.TacticsCtxSolverSimplify),[])
    ]