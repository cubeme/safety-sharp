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

namespace SafetySharp.SafetyAnalysisTestScript

module internal SatsParser =

    open FParsec
    open SafetySharp.GenericParsers
    open Sats
    open SafetySharp.EngineOptions
    
    type UserState = {
        LetBindings : Map<LetIdentifier,LetType>;
    }
        with
            static member initialUserState =
                {
                    UserState.LetBindings = Map.empty<LetIdentifier,LetType>;
                }
            member us.hasLetBinding (binding:LetIdentifier): bool =
                us.LetBindings.ContainsKey binding
            member us.isLetBindingOfType (binding:LetIdentifier) (letType:LetType): bool =
                if (us.LetBindings.ContainsKey binding) then
                    (us.LetBindings.Item binding) = letType
                else
                    false
            member us.addBinding (letIdentifier:LetIdentifier,letType:LetType) : UserState =
                { us with
                    LetBindings = us.LetBindings.Add(letIdentifier,letType)
                }                
          
                
    let spaces = SafetySharp.GenericParsers.spaces
    let spaces1 = SafetySharp.GenericParsers.spaces1

    let str_ws1 (str:string) = (pstring str) .>> spaces1
    let str_ws (str:string) = (pstring str) .>> spaces

    let parseUntilSemicolon<'us> : Parser<string,'us> = manySatisfy (fun c -> c <> ';')    
    let parseInQuotations<'us> : Parser<string,'us> = between (pchar '"') (pchar '"') (manySatisfy (fun c -> c <> '"'))
    
    let pfilename = parseInQuotations
    
    let parseInQuotations_ws = parseInQuotations .>> spaces
    let pfilename_ws = pfilename .>> spaces


    //////////////////////////////////////////////////////////
    //   DO
    //////////////////////////////////////////////////////////
    let parseDoStatement_SetEngineOption : Parser<DoStatement,UserState> =
        let standardVerifier =
            let nusmv = pstring "NuSMV" >>% ( (AtEngineOptions.StandardVerifier.NuSMV :> SafetySharp.EngineOptions.IEngineOption) |> DoStatement.SetEngineOption )
            let verifiers = nusmv
            (str_ws1 "standardVerifier") >>. nusmv
        let engineOptions =
            (attempt standardVerifier)
        (str_ws1 "setEngineOption") >>. engineOptions
                
    let parseDoStatement_SetMainModel : Parser<DoStatement,UserState> =
        (str_ws1 "setMainModel") >>.(pfilename_ws |>> DoStatement.SetMainModel)

    let parseDoStatement_SetEmptyMainModel : Parser<DoStatement,UserState> =
        (str_ws1 "setEmptyMainModel") >>.(parseInQuotations_ws |>> DoStatement.SetEmptyMainModel)
        
    let parseDoStatement_InjectSamModel : Parser<DoStatement,UserState> =
        (str_ws1 "injectSamModel") >>.((pfilename_ws .>>. parseInQuotations_ws) |>> DoStatement.InjectSamModel)
                  

    let parseDoStatement : Parser<DoStatement,UserState> =
        let doStatements =
            (attempt parseDoStatement_SetEngineOption) <|>
            (attempt parseDoStatement_SetMainModel) <|>
            (attempt parseDoStatement_SetEmptyMainModel) <|>
            (attempt parseDoStatement_InjectSamModel)
        (str_ws1 "do") >>. doStatements

        
    //////////////////////////////////////////////////////////
    //   LET
    //////////////////////////////////////////////////////////
        
    let parseLetIdentifierOfTypeDecl (letType:LetType) : Parser<LetIdentifier,UserState>=
        let parser (stream:CharStream<UserState>) =
            let parseIdentifier = identifier (IdentifierOptions())
            let parsedIdentifier = parseIdentifier stream
            if parsedIdentifier.Status = ReplyStatus.Ok then
                let identifier = parsedIdentifier.Result
                if not(stream.UserState.hasLetBinding identifier) then
                    stream.UserState <- stream.UserState.addBinding(identifier,letType)
                    Reply(parsedIdentifier.Status,identifier,parsedIdentifier.Error)
                else
                    let error = messageError (sprintf "LetIdentifier '%s' has already been declared" identifier)
                    Reply(ReplyStatus.Error,mergeErrors parsedIdentifier.Error error)
            else
                Reply(parsedIdentifier.Status,parsedIdentifier.Error)
        parser

        
    let parseLetIdentifierOfTypeInst (letType:LetType) : Parser<LetIdentifier,UserState>=
        let parser (stream:CharStream<UserState>) =
            let parseIdentifier = identifier (IdentifierOptions())
            let parsedIdentifier = parseIdentifier stream
            if parsedIdentifier.Status = ReplyStatus.Ok then
                if stream.UserState.isLetBindingOfType parsedIdentifier.Result letType then
                    Reply(parsedIdentifier.Status,parsedIdentifier.Result,parsedIdentifier.Error)
                else
                    let error = messageError (sprintf "LetIdentifier '%s' has not been declared or the kind of access is wrong" parsedIdentifier.Result)
                    Reply(ReplyStatus.Error,mergeErrors parsedIdentifier.Error error)
            else
                Reply(parsedIdentifier.Status,parsedIdentifier.Error)
        parser


    let parseLetStatement_AtLtlFormula : Parser<LetStatement,UserState> =
        let createLetStatement (letIdentifier:LetIdentifier) (formula:string) : LetStatement =
            LetStatement.AtLtlFormula(letIdentifier,formula)
        pipe2 ( (parseLetIdentifierOfTypeDecl LetType.LetTypePropertyResult) .>> spaces .>> (str_ws "=") .>> (str_ws1 "verifyLtl") )
              (parseInQuotations_ws)
              createLetStatement
              
    let parseLetStatement_AtDccaLtl : Parser<LetStatement,UserState> =
        let createLetStatement (letIdentifier:LetIdentifier) (hazard:string) : LetStatement =
            LetStatement.AtDccaLtl(letIdentifier,hazard)
        pipe2 ( (parseLetIdentifierOfTypeDecl LetType.LetTypeDccaResult) .>> spaces .>> (str_ws "=") .>> (str_ws1 "verifyDccaLtl") )
              (parseInQuotations_ws)
              createLetStatement

    let parseLetStatement : Parser<LetStatement,UserState> =        
        let letStatements =
            (attempt parseLetStatement_AtLtlFormula) <|>
            (attempt parseLetStatement_AtDccaLtl)
        (str_ws1 "let") >>. letStatements

        
    //////////////////////////////////////////////////////////
    //   Expect
    //////////////////////////////////////////////////////////
    
    let parseExpectStatement_ExpectPropertyResult : Parser<ExpectStatement,UserState> =
        let createLetStatement (letIdentifier:LetIdentifier) (result:SafetySharp.Ternary.Ternary) : ExpectStatement =
            ExpectStatement.ExpectPropertyResult(letIdentifier,result)
        let parseResult : Parser<SafetySharp.Ternary.Ternary,_> =
            (str_ws "valid" >>% SafetySharp.Ternary.Ternary.True) <|>
            (str_ws "invalid" >>% SafetySharp.Ternary.Ternary.False) <|>
            (str_ws "unknown" >>% SafetySharp.Ternary.Ternary.Unknown)
        pipe2 ( (parseLetIdentifierOfTypeInst LetType.LetTypePropertyResult) .>> (pstring ".") .>> (str_ws "result") .>> (str_ws "="))
              (parseResult)
              createLetStatement
    
    let parseExpectStatement : Parser<ExpectStatement,UserState> =               
        let expectStatements =
            (attempt parseExpectStatement_ExpectPropertyResult)
        (str_ws1 "expect") >>. expectStatements

        
    //////////////////////////////////////////////////////////
    //   Pgm
    //////////////////////////////////////////////////////////
    
    let parseSatsStatement : Parser<SatsStatement,UserState> =
        ((attempt parseDoStatement) |>> SatsStatement.DoStatement) <|>
        ((attempt parseLetStatement) |>> SatsStatement.LetStatement) <|>
        ((attempt parseExpectStatement) |>> SatsStatement.ExpectStatement)

    let parseSatsStatement_ws = parseSatsStatement .>> spaces .>> (pstring ";") .>> spaces
        

    let parseSatsPgm_ws: Parser<SatsPgm,UserState> =
        let createSatsPgm (stmnts:SatsStatement list) : SatsPgm =
            {
                SatsPgm.Pgm = stmnts;
                SatsPgm.LetBindings = Map.empty<LetIdentifier,LetType>
            }
        many parseSatsStatement_ws |>> createSatsPgm

    let parseSatsFile (str:string) : SatsPgm =
        let fileParser = spaces >>. parseSatsPgm_ws .>> eof    
        let parsedFile = runParserOnString fileParser UserState.initialUserState "" str
        match parsedFile with
            | Success(result, _, _)   -> result
            | Failure(errorMsg, a, b) -> failwith errorMsg

        
    open SafetySharp.Workflow
    open SafetySharp.Models.ScmTracer
    
    let parseSatsFileWorkflow () : ExogenousWorkflowFunction<string,SatsPgm> = workflow {
        let! model = SafetySharp.Workflow.getState ()
        let satsPgm = parseSatsFile model
        do! updateState satsPgm
    }