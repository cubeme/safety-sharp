// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineeringgineering
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
open SafetySharp.Models.Sam

//////////////////////////////////////////////////////////////////////////////
// helpers
//////////////////////////////////////////////////////////////////////////////
module internal SamToStringHelpers =
    type NewLineStyle =
        | NoNewLine
        | NewLine
        | NewParagraph

    type AstToStringState = {
        Indent : int;
        NewLineStyle : NewLineStyle;
        CurrentLine : System.Text.StringBuilder;
        TextBuffer : string list;
    }
        with
            static member initial =
                {
                    AstToStringState.Indent = 0;
                    AstToStringState.NewLineStyle = NewLineStyle.NoNewLine;
                    AstToStringState.CurrentLine = new System.Text.StringBuilder();
                    AstToStringState.TextBuffer = [];
                }                
            override state.ToString() : string =
                (state.CurrentLine.ToString() :: state.TextBuffer)
                    |> List.rev
                    |> String.concat System.Environment.NewLine

    type AstToStringStateFunction = AstToStringState -> AstToStringState

    //elementary

    let increaseIndent (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent + 1;
        }
    let decreaseIndent (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.Indent = state.Indent - 1;
        }
    let newLine (state:AstToStringState) : AstToStringState =
        let newLineStyle =
            match state.NewLineStyle with
                | NewLineStyle.NoNewLine -> NewLine
                | NewLineStyle.NewLine -> NewLine
                | NewLineStyle.NewParagraph -> NewParagraph //NewParagraph is stronger
        { state with
            AstToStringState.NewLineStyle = newLineStyle;
        }
    let newParagraph (state:AstToStringState) : AstToStringState =
        { state with
            AstToStringState.NewLineStyle = NewLineStyle.NewParagraph;
        }
        
    // this one gets executed automatically, when append is executed (see definition of append )
    // (it would also be possible to add it to (>>=) )
    let appendTrail (state:AstToStringState) : AstToStringState =
        match (state.NewLineStyle) with
            | NewLineStyle.NoNewLine ->
                state
            | NewLineStyle.NewLine ->
                { state with
                    AstToStringState.TextBuffer = state.CurrentLine.ToString() :: state.TextBuffer
                    AstToStringState.CurrentLine = new System.Text.StringBuilder( String.replicate state.Indent "  " );
                    AstToStringState.NewLineStyle = NewLineStyle.NoNewLine;
                }
            | NewLineStyle.NewParagraph ->
                { state with
                    AstToStringState.TextBuffer = ""::state.CurrentLine.ToString()::state.TextBuffer
                    AstToStringState.CurrentLine = new System.Text.StringBuilder(String.replicate state.Indent "  ");
                    AstToStringState.NewLineStyle = NewLineStyle.NoNewLine;
                }
        

    let append (str:string) (state:AstToStringState) : AstToStringState =
        let newState = appendTrail state
        { newState with
            AstToStringState.CurrentLine = newState.CurrentLine.Append(str);
        }

    let rec foreach (elements:'a list) (writer: 'a -> AstToStringState -> AstToStringState) (state:AstToStringState): AstToStringState =
        if elements.IsEmpty then
            state
        else
            let newState = writer elements.Head state
            foreach elements.Tail writer newState

    let rec foreachWithSep  (elements:'a list) (writer: 'a -> AstToStringState -> AstToStringState) (sep:AstToStringState -> AstToStringState) (state:AstToStringState): AstToStringState =
        if elements.IsEmpty then
            state
        else if elements.Tail.IsEmpty then
            writer elements.Head state
        else
            let newState1 = writer elements.Head state
            let newState2 = sep newState1
            foreachWithSep elements.Tail writer sep newState2

    
    // Inspired by FParsec's createParserForwardedToRef (defined in FParsec/Primitives.fs)
    let createWriterForwardedToRef() =
        let dummyWriter = fun (state:AstToStringState) ->
            failwith "the writerRef needs to be replaced by a real implementation"
        let w = ref dummyWriter
        ((fun state -> !w state), w) : AstToStringStateFunction * AstToStringStateFunction ref
    

    // Inspired by http://fsharpforfunandprofit.com/posts/computation-expressions-bind/
    let (>>=) (m:AstToStringStateFunction)
              (f:AstToStringStateFunction)
              (state:AstToStringState) : AstToStringState =
        let newState = m state
        f newState
        // alternative:
        //  let newStateWithTrail = appendTrail newState
        //  f newStateWithTrail
    

    
    // convenience    
    let whitespace : AstToStringStateFunction =
        append " "

        
    let newLineAndIncreaseIndent : AstToStringStateFunction =
        newLine >>= increaseIndent

    let newLineAndDecreaseIndent : AstToStringStateFunction =
        newLine >>= decreaseIndent
            
    let private splitStringIntoTokens (str:string) : string array =
        // in the result between two elements there was a %s
        let stringLength = str.Length
        let currentToken = new System.Text.StringBuilder()
        let rec splitString (revProcessedTokens:string list) (currentPosition:int,previousWasPercent:bool) : string list =
            if currentPosition = stringLength then
                let lastToken = currentToken.ToString ()
                let completeRev = lastToken :: revProcessedTokens
                completeRev |> List.rev
            else
                let currentChar = str.Chars currentPosition
                let currentIsPercent = (currentChar = '%')
                match (previousWasPercent,currentChar) with
                    | (true,'%') ->
                        do currentToken.Append(currentChar) |> ignore
                        splitString revProcessedTokens (currentPosition+1,false)
                    | (true,'s') ->
                        let completeToken = currentToken.ToString()
                        do currentToken.Clear() |> ignore
                        let newRevProcessedTokens = completeToken :: revProcessedTokens
                        splitString newRevProcessedTokens (currentPosition+1,false)
                    | (true,_) ->
                        failwith "Not expected anything else than %s in a format string at this point"
                    | (false,'%') ->
                        splitString revProcessedTokens (currentPosition+1,true)
                    | (false,currentChar) ->
                        do currentToken.Append(currentChar) |> ignore
                        splitString revProcessedTokens (currentPosition+1,false)
        splitString [] (0,false) |> Array.ofList
        
    let splitStringIntoTokensBuffer = new System.Collections.Generic.Dictionary<string,string array> ()
    let private splitStringIntoTokens_buffered (str:string) : string array =
        if splitStringIntoTokensBuffer.ContainsKey str then
            splitStringIntoTokensBuffer.Item str
        else
            let newElement = splitStringIntoTokens str
            do splitStringIntoTokensBuffer.Add(str,newElement)
            newElement
            
    let mprintf0 : Printf.StringFormat<string> -> AstToStringStateFunction =
        let behavior (stringFormat:Printf.StringFormat<string>) : AstToStringStateFunction =
            append stringFormat.Value
        behavior

    let mprintf1 : Printf.StringFormat<string->string> -> AstToStringStateFunction -> AstToStringStateFunction =
        let behavior (stringFormat:Printf.StringFormat<string->string>) (elem1:AstToStringStateFunction) : AstToStringStateFunction =            
            let splitted = splitStringIntoTokens_buffered stringFormat.Value
            assert (splitted.Length = 2)
            append (splitted.[0]) >>= elem1 >>= append (splitted.[1])
        behavior
        
    let mprintf2 : Printf.StringFormat<string->string->string> -> AstToStringStateFunction -> AstToStringStateFunction -> AstToStringStateFunction =
        let behavior (stringFormat:Printf.StringFormat<string->string->string>) (elem1:AstToStringStateFunction) (elem2:AstToStringStateFunction) : AstToStringStateFunction =            
            let splitted = splitStringIntoTokens_buffered stringFormat.Value
            assert (splitted.Length = 3)
            append (splitted.[0]) >>= elem1 >>= append (splitted.[1]) >>= elem2 >>= append (splitted.[2])
        behavior
        
    let mprintf3 : Printf.StringFormat<string->string->string->string> -> AstToStringStateFunction -> AstToStringStateFunction -> AstToStringStateFunction -> AstToStringStateFunction =
        let behavior (stringFormat:Printf.StringFormat<string->string->string->string>) (elem1:AstToStringStateFunction) (elem2:AstToStringStateFunction) (elem3:AstToStringStateFunction) : AstToStringStateFunction =            
            let splitted = splitStringIntoTokens_buffered stringFormat.Value
            assert (splitted.Length = 4)
            append (splitted.[0]) >>= elem1 >>= append (splitted.[1]) >>= elem2 >>= append (splitted.[2]) >>= elem3 >>= append (splitted.[3])
        behavior

    let mprintf4 : Printf.StringFormat<string->string->string->string->string> -> AstToStringStateFunction -> AstToStringStateFunction -> AstToStringStateFunction -> AstToStringStateFunction -> AstToStringStateFunction =
        let behavior (stringFormat:Printf.StringFormat<string->string->string->string->string>) (elem1:AstToStringStateFunction) (elem2:AstToStringStateFunction) (elem3:AstToStringStateFunction) (elem4:AstToStringStateFunction) : AstToStringStateFunction =            
            let splitted = splitStringIntoTokens_buffered stringFormat.Value
            assert (splitted.Length = 5)
            append (splitted.[0]) >>= elem1 >>= append (splitted.[1]) >>= elem2 >>= append (splitted.[2]) >>= elem3 >>= append (splitted.[3]) >>= elem4 >>= append (splitted.[4])
        behavior

module internal SamToString =
    open SamToStringHelpers
    
    let realFormat = new System.Globalization.CultureInfo("en-US")

    //////////////////////////////////////////////////////////////////////////////
    // actual export
    //////////////////////////////////////////////////////////////////////////////
     
    let exportVar (var:Var) : AstToStringStateFunction =
        let toAppend =
            match var with
                | Var(str) -> str
        append toAppend
       
       
    let exportUOp (uop:UOp) : AstToStringStateFunction =
        let toAppend =
            match uop with
                //| UOp.Minus -> "-"
                | UOp.Not -> "!"
        append toAppend

    let exportBOp (bop:BOp) : AstToStringStateFunction =
        let toAppend =
            match bop with
                | BOp.Add -> "+"
                | BOp.Subtract -> "-"
                | BOp.Multiply -> "*"
                | BOp.Divide -> "/"
                | BOp.Modulo -> "%"
                | BOp.And -> "&&"
                | BOp.Or -> "||"
                | BOp.Implies -> "->"
                | BOp.Equals -> "=="
                | BOp.NotEquals -> "!="
                | BOp.Less -> "<"
                | BOp.LessEqual -> "<="
                | BOp.Greater -> ">"
                | BOp.GreaterEqual -> ">="
        append toAppend
         
    let exportVal (_val:Val) : AstToStringStateFunction =
        let toAppend =
            match _val with
                | Val.BoolVal (_val) ->
                    match _val with
                        | true -> "true"
                        | false -> "false"
                | Val.NumbVal (_val) -> _val.ToString()
                | Val.RealVal (_val) -> System.Convert.ToString(_val,realFormat)
                | Val.ProbVal (_val) -> System.Convert.ToString(_val,realFormat)
        append toAppend

    let exportElement (elem:Element) : AstToStringStateFunction =
        match elem with
            | Element.GlobalVar (_var) -> exportVar _var
            | Element.LocalVar (_var) -> exportVar _var

    let rec exportExpr (expr:Expr) : AstToStringStateFunction =
        match expr with
            | Expr.Literal (_val) -> exportVal  _val
            | Expr.Read (elem) -> exportElement elem
            | Expr.ReadOld (elem) -> (append "prev(") >>= (exportElement elem) >>= (append ")")
            | Expr.UExpr (expr,uop) ->                
                //sprintf "%s(%s)" (exportUOp state uop)  (exportExpr state expr)
                (exportUOp uop) >>= (append "(") >>= (exportExpr expr) >>= (append ")")
            | Expr.BExpr (exprLeft, bop, exprRight) ->
                (append "(") >>= (exportExpr exprLeft) >>= (append ")")  >>=
                (exportBOp bop) >>=
                (append "(") >>= (exportExpr exprRight) >>= (append ")") 
            | Expr.IfThenElseExpr (guardExpr, thenExpr, elseExpr) ->
                (append "(") >>= (exportExpr guardExpr) >>= (append ") ?")  >>=
                (append "(") >>= (exportExpr thenExpr) >>= (append ") :")  >>=
                (append "(") >>= (exportExpr elseExpr) >>= (append ")") 
       
    let rec exportStm (stm:Stm) : AstToStringStateFunction =
        match stm with
            | Stm.Block (stmts) ->
                newLine >>= (append "{") >>= newLineAndIncreaseIndent >>= 
                (foreach stmts (fun stm -> exportStm stm >>= newLine)) >>=
                decreaseIndent >>= (append "}") >>= newLine
            | Stm.Choice (choices:Clause list) ->
                newLine >>= (append "choice {") >>= newLineAndIncreaseIndent >>= 
                (foreach choices (fun clause -> 
                                       exportExpr clause.Guard >>= append " => " >>= exportStm clause.Statement >>= newLine)
                                 ) >>=
                decreaseIndent >>= (append "}") >>= newLine
            | Stm.Stochastic (stochasticChoices) ->
                newLine >>= (append "stochastic {") >>= newLineAndIncreaseIndent >>= 
                (foreach stochasticChoices
                    (fun (probExpr,stm) -> 
                        exportExpr probExpr >>= append " => " >>= exportStm stm >>= newLine)
                    ) >>=
                decreaseIndent >>= (append "}") >>= newLine                
            | Stm.Write (elem,expr) ->
                (exportElement elem) >>=
                (append " := ") >>=
                (exportExpr expr) >>=
                (append "; ")
           
    let exportType (_type:Type) : AstToStringStateFunction =
        let onOverrun _overflow = 
            match _overflow with
                | OverflowBehavior.Error -> "error"
                | OverflowBehavior.WrapAround -> "wrap around"
                | OverflowBehavior.Clamp -> "clamp"
                | _ -> failwith "NotImplementedYet"
        match _type with
            | BoolType -> append "bool"
            | IntType -> append "int"
            | RealType -> append "real"
            | RangedIntType(_from,_to,_overflow) ->
                let newType = sprintf "int<%d..%d,%s on overrun>" _from _to (onOverrun _overflow)
                append newType
            | RangedRealType(_from,_to,_overflow) ->
                //https://msdn.microsoft.com/en-us/library/ee370560.aspx
                let newType = sprintf "real<%s..%s,%s on overrun>" (System.Convert.ToString(_from,realFormat)) (System.Convert.ToString(_to,realFormat)) (onOverrun _overflow)
                append newType


    let exportLocalVarDecl (varDecl:LocalVarDecl) : AstToStringStateFunction =
        (exportType varDecl.Type) >>=
        (whitespace) >>=
        (exportVar varDecl.Var) >>=
        (append ";") >>= newLine

    let exportGlobalVarDecl (varDecl:GlobalVarDecl): AstToStringStateFunction =
        (exportType varDecl.Type) >>=
        (whitespace) >>=
        (exportVar varDecl.Var) >>=
        (whitespace) >>=
        (foreachWithSep varDecl.Init exportVal (append ",") ) >>=
        (append ";")
    
        
    let rec exportPgm (pgm:Pgm) : AstToStringStateFunction =
        (append "globals {") >>= (newLineAndIncreaseIndent) >>=
        (foreachWithSep pgm.Globals exportGlobalVarDecl (newLine) ) >>=
        (newLineAndDecreaseIndent) >>= (append "}") >>= newParagraph >>=
        (append "locals {") >>= (newLineAndIncreaseIndent) >>=
        (foreachWithSep pgm.Locals  exportLocalVarDecl  (newParagraph) ) >>=
        (newLineAndDecreaseIndent) >>= (append "}") >>= newParagraph >>=
        (exportStm pgm.Body )


    let exportModel (pgm:Pgm) : string =
        let stateAfterExport =
            exportPgm pgm AstToStringState.initial
        stateAfterExport.ToString()
        

    open SafetySharp.Workflow
    open SafetySharp.Models.SamTracer
    
    let modelToStringWorkflow<'traceableOfOrigin> () : WorkflowFunction<SamTracer<'traceableOfOrigin>,string,unit> = workflow {
        let! model = getState ()
        let asString = exportModel (model.Pgm)
        do! updateState asString
    }

