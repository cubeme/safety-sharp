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

module Z3ExampleDatatypes

open SafetySharp.Internal.SmtSolving.SmtLib2.Ast
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser
open SafetySharp.Internal.SmtSolving.SmtLib2.Parser.SmtLib2ParsingResult
open SafetySharp.Internal.SmtSolving.SmtLib2.SMTLIB2Convenience
open SafetySharp.Internal.SmtSolving.Z3.Ast
open SafetySharp.Internal.SmtSolving.Z3.Parser


//I think this isn't exported correctly at location "(Tree leaf (node (..."
let exampleTutorialMutuallyRecursiveDatatypes : DeclareDataTypes =
    { DeclareDataTypes.formalParameters=[Symbol.Symbol("T")];
      DeclareDataTypes.datatypes=[{ DatatypeDeclaration.nameOfDatatype=Symbol.Symbol("Tree");
                                    DatatypeDeclaration.constructors=[ {ConstructorDecl.constructorName=Symbol.Symbol("leaf");
                                                                        ConstructorDecl.content=[]
                                                                       };
                                                                       {ConstructorDecl.constructorName=Symbol.Symbol("node");
                                                                        ConstructorDecl.content=[{AccessorDecl.accessPartialContentFunctionName=Symbol.Symbol("value");
                                                                                                  AccessorDecl.typeOfPartialContent=SortFromString "T"
                                                                                                 };
                                                                                                 {AccessorDecl.accessPartialContentFunctionName=Symbol.Symbol("children");
                                                                                                  AccessorDecl.typeOfPartialContent=SortFromString "TreeList"
                                                                                                 }
                                                                                                ]
                                                                       }
                                                                     ]
                                  };
                                  { DatatypeDeclaration.nameOfDatatype=Symbol.Symbol("TreeList");
                                    DatatypeDeclaration.constructors=[ {ConstructorDecl.constructorName=Symbol.Symbol("nil");
                                                                        ConstructorDecl.content=[]
                                                                       };
                                                                       {ConstructorDecl.constructorName=Symbol.Symbol("cons");
                                                                        ConstructorDecl.content=[{AccessorDecl.accessPartialContentFunctionName=Symbol.Symbol("car");
                                                                                                  AccessorDecl.typeOfPartialContent=SortFromString "Tree"
                                                                                                 };
                                                                                                 {AccessorDecl.accessPartialContentFunctionName=Symbol.Symbol("cdr");
                                                                                                  AccessorDecl.typeOfPartialContent=SortFromString "TreeList"
                                                                                                 }
                                                                                                ]
                                                                       }
                                                                     ]
                                  };
                                 ]
    }