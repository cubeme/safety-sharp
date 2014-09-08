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

namespace SafetySharp.Internal.Modelchecking.Prism

// semantics of prism
// http://www.prismmodelchecker.org/doc/semantics.pdf

// source for AST:
// http://www.prismmodelchecker.org/manual/ThePRISMLanguage/Introduction


// Chapter Constants
type Constant =
    | Integer of int
    | Double of double
    | Boolean of bool

// Chapter Expressions
type SimpleExpression =
    string


// Chapter Modules And Variables
type Identifier = {
    Name : string;
}
    with
        static member reserved = [ "A"; "bool"; "clock"; "const"; "ctmc"; "C"; "double"; "dtmc"; "E"; "endinit"; "endinvariant"; "endmodule"; "endrewards"; "endsystem"; "false"; "formula"; "filter"; "func"; "F"; "global"; "G"; "init"; "invariant"; "I"; "int"; "label"; "max"; "mdp"; "min"; "module"; "X"; "nondeterministic"; "Pmax"; "Pmin"; "P"; "probabilistic"; "prob"; "pta"; "rate"; "rewards"; "Rmax"; "Rmin"; "R"; "S"; "stochastic"; "system"; "true"; "U"; "W"]


[<RequireQualifiedAccess>]
type VariableType =
    | Bool
    | IntRange of From:int * To:int
    | Int //only usable in few kinds of model analysis (e.g. simulation)

type VariableDeclaration = {
    // A variable declaration in a module
    Name : Identifier;
    Type : VariableType;
    InitialValue : string option; //when initial value is omitted"; "lowest value is assumed (!= NuXmv where indeterministic intial value is assumed)
}

type Module = {
    Name : Identifier;
}

// Chapter Constants
type ConstantDeclaration = {
    Name : Identifier;
    //Type : 
    Value : SimpleExpression;
}

// Chapter Commands

type Update =
    //equivalent examples for an update (unnecessary things can be left out):
    //    (x1'=x1)&(x2'=x2)
    //    (x1'=x1)
    //    true
    (Identifier * SimpleExpression) list

type Command = {
    // Example for a Command: "[] x=0 -> 0.8:(x'=0) + 0.2:(x'=1);"
    // where "x=0" is a guard,
    //       "x'=0" is an update
    //       "0.8" is the associated probability of update "x'=0"
    // Another deterministic example: "[] x=1 & y!=2 -> (x'=2);"
    //        This is equivalent to "[] x=1 & y!=2 -> 1.0:(x'=2);"
    // A CTMC example: "[] x=0 -> 50:(x'=1) + 60:(x'=2);"
    //       "50" is the associate rate of update "x'=1"
    Guard : string;
}

// Parallel Composition
type Choice =
    | NondeterministicChoice // MDP
    | ProbabilisticChoice // DTMC
    | RaceCondition // CTMC

// CTMC
type ProbabilityOrRate =
    | Probability //MDP, DTMC
    | Rate //CTMC