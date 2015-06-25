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

namespace SafetySharp.Models

module internal ScmVeParser =
    open FParsec
    open SafetySharp.Models.Scm
    open SafetySharp.Models.ScmHelpers
    open SafetySharp.Models.ScmVerificationElements
    open SafetySharp.GenericParsers
    
    [<RequireQualifiedAccess>]
    type IdentifierType =
        | Field
        | Var
        | Fault
        | Comp
        | NotDeclared
        

    type UserState = {
        CurrentLocation : CompPath;
        LocationToType : Map<CompPath*string,IdentifierType> ;
    }
        with
            member us.IsFullLocationOfType (location:CompPath*string) (id_type:IdentifierType) =
                if not(us.LocationToType.ContainsKey location) then
                    false
                else if (us.LocationToType.ContainsKey location) && (us.LocationToType.Item location = id_type) then
                    true
                else
                    false
            member us.IsIdentifierInCurrentLocationOfType (identifier:string) (id_type:IdentifierType) =
                let locationToCheck = us.CurrentLocation,identifier
                us.IsFullLocationOfType locationToCheck
            member us.pushCurrentLocation (compName:Comp) : UserState =
                { us with
                    UserState.CurrentLocation = compName::us.CurrentLocation;
                }                
            member us.popCurrentLocation : UserState =
                { us with
                    UserState.CurrentLocation = us.CurrentLocation.Tail;
                }
            member us.resetCurrentLocation : UserState =
                { us with
                    UserState.CurrentLocation = [];
                }
            static member initialUserState (scmModel:Scm.ScmModel) =
                let rec collectLocationsOfIdentifiers (parentLocation:CompPath) (currentCompDecl:CompDecl) : ((CompPath*string)*IdentifierType) list =
                    let currentLocation = (currentCompDecl.Comp)::parentLocation
                    let identifiersFromSubs = currentCompDecl.Subs |> List.collect (collectLocationsOfIdentifiers currentLocation)
                    let identifiersFromHere =
                        let identifierFromFields = currentCompDecl.Fields |> List.map (fun field -> ((currentLocation,field.getName),IdentifierType.Field)  )
                        let identifierFromFaults = currentCompDecl.Faults |> List.map (fun fault -> ((currentLocation,fault.getName),IdentifierType.Fault) )
                        let identifierFromComp = ((parentLocation,currentCompDecl.Comp.getName),IdentifierType.Comp)
                        (identifierFromComp::identifierFromFields@identifierFromFaults)
                    (identifiersFromHere@identifiersFromSubs)
                let rootComponent = scmModel.getRootComp
                let locatedIdentifiers = collectLocationsOfIdentifiers []  (rootComponent)
                {
                    UserState.CurrentLocation = [];
                    UserState.LocationToType =  locatedIdentifiers |> Map.ofList;
                }
                
    let boolVal<'us> : Parser<_,'us> = ScmParser.boolVal
    let numberVal<'us> : Parser<_,'us> = ScmParser.numberVal
    let realVal<'us> : Parser<_,'us> = ScmParser.realVal
    let value<'us> : Parser<_,'us> = ScmParser.value        
    let probVal<'us> : Parser<_,'us> = ScmParser.probVal
    let parseIdentifier = ScmParser.parseIdentifier

    let parseIdStartCharOrDot<'us> : Parser<_,'us> =
        satisfy (fun char -> (ScmParser.isIdentifierStart char) || (char='.') )
    
    let parseLocation : Parser<_,UserState> =
        // TODO: could check, if path is correct
        (many1 (attempt (parseIdentifier |>> Comp.Comp .>> pstring "." ))) |>> List.rev
                        
    let parseLocatedIdentifierInst (id_type:IdentifierType) : Parser<_,UserState> =
        fun stream ->
            let locationIdentifierReply = (parseLocation .>>. parseIdentifier) stream
            if locationIdentifierReply.Status = ReplyStatus.Ok then
                let (location,identifier) = locationIdentifierReply.Result
                if stream.UserState.IsFullLocationOfType (location,identifier) id_type then
                    Reply(locationIdentifierReply.Status,(location,identifier),locationIdentifierReply.Error)
                else
                    let error = messageError (sprintf "Identifier '%s' has not been declared in path %s or the kind of access is wrong" identifier (location |> List.rev |> List.map (fun (Comp(c)) -> c) |> String.concat ".") )
                    Reply(ReplyStatus.Error,mergeErrors locationIdentifierReply.Error error)
            else
                Reply(locationIdentifierReply.Status,locationIdentifierReply.Error)
                
                
    let locFieldInst: Parser<_,UserState> = parseLocatedIdentifierInst IdentifierType.Field
    let locFaultInst: Parser<_,UserState> = parseLocatedIdentifierInst IdentifierType.Fault
    
    
    let str_ws a = (pstring a) .>> spaces
    let locFieldInst_ws = locFieldInst .>> spaces
    let locFaultInst_ws = locFaultInst .>> spaces
    let boolVal_ws<'us> : Parser<_,'us> = ScmParser.boolVal_ws
    let numberVal_ws<'us> = ScmParser.numberVal_ws
    let value_ws<'us> : Parser<_,'us> = ScmParser.value_ws    
    let probVal_ws<'us> : Parser<_,'us> = ScmParser.probVal_ws

    let parentOpen_ws = str_ws "("
    let parentClose_ws = str_ws ")"
                
    // parses a propositional expression
    let propositionalExprParser : Parser<_,UserState> =
        let opp = new OperatorPrecedenceParser<_,_,UserState>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 5, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 5, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Multiply, e2)))
        opp.AddOperator(InfixOperator("%"   , spaces , 5, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Modulo, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 4, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Add, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">" , 4, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Subtract, e2)))
        // >
        opp.AddOperator(InfixOperator("<="  , spaces , 3, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.LessEqual, e2)))
        opp.AddOperator(InfixOperator("=="  , spaces , 3, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Equals, e2)))
        opp.AddOperator(InfixOperator("=/=" , spaces , 3, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.NotEquals, e2)))
        opp.AddOperator(InfixOperator(">="  , spaces , 3, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.GreaterEqual, e2)))
        opp.AddOperator(InfixOperator(">"   , spaces , 3, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Greater, e2)))
        opp.AddOperator(InfixOperator("<"   , spaces , 3, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Less, e2)))
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> PropositionalExpr.UExpr(e,UOp.Not)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.And, e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> PropositionalExpr.BExpr(e1, BOp.Or, e2)))

        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)
        
        // recursive term parser for expressions
        opp.TermParser <-
            (boolVal_ws |>> PropositionalExpr.Literal) <|> 
            (numberVal_ws |>> PropositionalExpr.Literal) <|>
            (attempt locFieldInst_ws |>> (fun (loc,id) -> PropositionalExpr.ReadField(loc,Field.Field(id)) )) <|>
            (attempt locFaultInst_ws |>> (fun (loc,id) -> PropositionalExpr.ReadFault(loc,Fault.Fault(id)) ))<|> 
            (parenExpr_ws)

        opp.ExpressionParser
        
    // parses a ltl expression
    //   we use this precedence order: unary operators bind stronger than the binary operators.
    //   Temporal unary operator bind equally strong as propositional "Not". Until binds stronger than the binary propositional operators.

    let ltlExprParser : Parser<_,UserState> =
        let opp = new OperatorPrecedenceParser<_,_,UserState>()        
        opp.AddOperator(InfixOperator("/"   , spaces , 6, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Divide, e2)))
        opp.AddOperator(InfixOperator("*"   , spaces , 6, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Multiply, e2)))
        opp.AddOperator(InfixOperator("%"   , spaces , 6, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Modulo, e2)))
        // >
        opp.AddOperator(InfixOperator("+"   , spaces , 5, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Add, e2)))
        opp.AddOperator(InfixOperator("-"   , spaces .>> notFollowedByString ">" , 5, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Subtract, e2)))
        // >
        opp.AddOperator(InfixOperator("U"  , (notFollowedBy parseIdStartCharOrDot) .>> spaces , 4, Associativity.Left, fun e1 e2 -> LtlExpr.LbExpr(e1, LbOp.Until, e2)))
        // >
        opp.AddOperator(InfixOperator("<="  , spaces , 3, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.LessEqual, e2)))
        opp.AddOperator(InfixOperator("=="  , spaces , 3, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Equals, e2)))
        opp.AddOperator(InfixOperator("=/=" , spaces , 3, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.NotEquals, e2)))
        opp.AddOperator(InfixOperator(">="  , spaces , 3, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.GreaterEqual, e2)))
        opp.AddOperator(InfixOperator(">"   , spaces , 3, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Greater, e2)))
        opp.AddOperator(InfixOperator("<"   , spaces , 3, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Less, e2)))
        opp.AddOperator(PrefixOperator("!", spaces, 3, true, fun e -> LtlExpr.UExpr(e,UOp.Not)))
        opp.AddOperator(PrefixOperator("X", (notFollowedBy parseIdStartCharOrDot) .>> spaces, 3, true, fun e -> LtlExpr.LuExpr(e,LuOp.Next)))
        opp.AddOperator(PrefixOperator("G", (notFollowedBy parseIdStartCharOrDot) .>> spaces, 3, true, fun e -> LtlExpr.LuExpr(e,LuOp.Globally)))
        opp.AddOperator(PrefixOperator("F", (notFollowedBy parseIdStartCharOrDot) .>> spaces, 3, true, fun e -> LtlExpr.LuExpr(e,LuOp.Eventually)))
        //>
        opp.AddOperator(InfixOperator("&&"   , spaces , 2, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.And, e2)))
        //>
        opp.AddOperator(InfixOperator("||"   , spaces , 1, Associativity.Left, fun e1 e2 -> LtlExpr.BExpr(e1, BOp.Or, e2)))

        // parses an expression between ( and )
        let parenExpr_ws = between parentOpen_ws parentClose_ws (opp.ExpressionParser)
        
        // recursive term parser for expressions
        opp.TermParser <-
            (boolVal_ws |>> LtlExpr.Literal) <|> 
            (numberVal_ws |>> LtlExpr.Literal) <|>
            (attempt locFieldInst_ws |>> (fun (loc,id) -> LtlExpr.ReadField(loc,Field.Field(id)) )) <|>
            (attempt locFaultInst_ws |>> (fun (loc,id) -> LtlExpr.ReadFault(loc,Fault.Fault(id)) ))<|> 
            (parenExpr_ws)

        opp.ExpressionParser