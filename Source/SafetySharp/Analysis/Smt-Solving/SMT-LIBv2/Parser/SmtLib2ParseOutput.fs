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

namespace SafetySharp.Internal.SmtSolving.SmtLib2.Parser

open System
open System.IO
open FParsec
open SafetySharp.Internal.SmtSolving.SmtLib2.Ast
open ParseSMTLIB2Whitespace

type internal SMTOutputParser() =
    let cmn = SMTCommonParser()

    // Helpers
    let parseGenResponseIntern =
        choice [ str "unsupported"                      >>% GenResponse.GenResponseUnsupported;
                 str "success"                          >>% GenResponse.GenResponseSuccess;
                 str "error" >>. smt2ws >>. cmn.parseString |>> GenResponse.GenResponseError
               ]

    let parseErrorBehaviorIntern =
        choice [ str "immediate-exit"      >>% ErrorBehavior.ImmediateExit;
                 str "continued-execution" >>% ErrorBehavior.ContinuedExecution
               ]

    let parseReasonUnknownIntern =
        choice [ str "memout"     >>% ReasonUnknown.ReasonUnknownMemout;
                 str "incomplete" >>% ReasonUnknown.ReasonUnknownIncomplete
               ]

    let parseStatusIntern =
        choice [ str "sat"     >>% Status.StatusSat;
                 str "unsat"   >>% Status.StatusUnsat;
                 str "unknown" >>% Status.StatusUnknown
               ]

    // Parse Scripts Part 2: Command Responses
    let parseGetInfoResponseIntern : Parser<GetInfoResponse,unit> =
        let parseInfoResponse =
            choice [ str_smt2ws "error-behavior" >>. parseErrorBehaviorIntern |>> InfoResponse.InfoResponseErrorBehavior;
                     str_smt2ws "name"           >>. cmn.parseString          |>> InfoResponse.InfoResponseName;
                     str_smt2ws "authors"        >>. cmn.parseString          |>> InfoResponse.InfoResponseAuthors;
                     str_smt2ws "version"        >>. cmn.parseString          |>> InfoResponse.InfoResponseVersion;
                     str_smt2ws "reason-unknown" >>. parseReasonUnknownIntern |>> InfoResponse.InfoResponseReasonUnknown;
                     cmn.parseAttribute                                   |>> InfoResponse.InfoResponseAttribute
                   ]
        between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
            (many1 (parseInfoResponse .>> smt2ws))
    
    let parseCheckSatResponseIntern : Parser<CheckSatResponse,unit> =
        parseStatusIntern
    
    let parseGetAssertionsResponseIntern : Parser<GetAssertionsResponse,unit> =
        between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
            (many (cmn.parseTerm .>> smt2ws))
    
    let parseGetProofResponseIntern : Parser<GetProofResponse,unit> =
        let parseProof = 
            cmn.parseSExpr
        parseProof
    
    let parseGetUnsatCoreResponseIntern : Parser<GetUnsatCoreResponse,unit> =
        between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
            (many (cmn.parseSymbol .>> smt2ws))
    
    let parseGetValueResponseIntern : Parser<GetValueResponse,unit> =
        let parseValuationPair =
            between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
                ((cmn.parseTerm .>> smt2ws) .>>. (cmn.parseTerm .>> smt2ws))
        between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
            (many1 (parseValuationPair .>> smt2ws ))
    
    let parseGetAssignmentResponseIntern : Parser<GetAssignmentResponse,unit> =
        let parseTValuationPair =
            between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
                ((cmn.parseSymbol .>> smt2ws) .>>. (cmn.parseBValue .>> smt2ws))
        between (str "(" >>. smt2ws) (str ")" >>. smt2ws)
            (many (parseTValuationPair .>> smt2ws ))
    
    let parseGetOptionResponseIntern : Parser<GetOptionResponse,unit> =
        cmn.parseAttributeValue
    
    // Helpers
    member this.parseGenResponse   : Parser<_,unit> = parseGenResponseIntern
    member this.parseErrorBehavior : Parser<_,unit> = parseErrorBehaviorIntern
    member this.parseReasonUnknown : Parser<_,unit> = parseReasonUnknownIntern
    member this.parseStatus        : Parser<_,unit> = parseStatusIntern

    // Scripts Part 2: Command Responses    
    member this.parseGetInfoResponse       : Parser<_,unit> = parseGetInfoResponseIntern
    member this.parseCheckSatResponse      : Parser<_,unit> = parseCheckSatResponseIntern
    member this.parseGetAssertionsResponse : Parser<_,unit> = parseGetAssertionsResponseIntern
    member this.parseGetProofResponse      : Parser<_,unit> = parseGetProofResponseIntern
    member this.parseGetUnsatCoreResponse  : Parser<_,unit> = parseGetUnsatCoreResponseIntern
    member this.parseGetValueResponse      : Parser<_,unit> = parseGetValueResponseIntern
    member this.parseGetAssignmentResponse : Parser<_,unit> = parseGetAssignmentResponseIntern
    member this.parseGetOptionResponse     : Parser<_,unit> = parseGetOptionResponseIntern