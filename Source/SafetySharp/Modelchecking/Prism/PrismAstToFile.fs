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

open System

type internal ExportPrismAstToFile() =


    let indent (number:int) : string =
        let s=System.Text.StringBuilder ()
        for i = 1 to number do 
            s.Append "  " |> ignore
        s.ToString ()

    let nl = Environment.NewLine
    
    let nli (i:int) =
        nl + (indent i)
        
    let joinWithWhitespace (lst:string list) : string =
        String.Join(" ", lst)

    let joinWithComma (lst:string list) : string =
        String.Join(", ", lst)
    
    let joinWithNewLine (lst:string list) : string =
        String.Join("\n", lst)

    let joinWithIndentedNewLine (indent:int) (lst:string list): string =
        let indents = String.replicate indent "\t"
        let separator = "\n"+indents
        String.Join(separator, lst)
        
    let joinWith (operator:string) (lst:string list) : string =
        String.Join(operator, lst)


        
    member this.ExportConstant (constant : Constant) = 
        match constant with
            | Integer (_int) -> _int.ToString()
            | Double (_double) -> _double.ToString()
            | Boolean (_bool) -> _bool.ToString()
    
    member this.ExportIdentifier (identifier : Identifier) = 
        identifier.Name



        

    ///////////////////////////
    // MODEL
    ///////////////////////////
    
    //TODO: Property and label with ""

    member this.ExportExpression (expression : Expression) : string =
        match expression with
            | Expression.Constant (constant:Constant) ->
                this.ExportConstant constant
            | Expression.Variable (name:Identifier) ->
                this.ExportIdentifier name
            | Expression.Formula (name:Identifier) ->
                this.ExportIdentifier name
            // Expressions with operators known from Propositional Logic
            | Expression.UnaryNegation  (operand:Expression) ->                                 // !
                sprintf "!(%s)" (this.ExportExpression operand)
            | Expression.BinaryMultiplication (left:Expression, right:Expression) ->             // *
                sprintf "(%s)*(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryDivision (left:Expression, right:Expression) ->                   // / be cautious: Always performs floating point operation. 22/7 is 3.14... instead (3, even on integers
                sprintf "(%s)/(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryAddition (left:Expression, right:Expression) ->                   // +
                sprintf "(%s)+(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinarySubstraction (left:Expression, right:Expression) ->               // -
                sprintf "(%s)-(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryLessThan (left:Expression, right:Expression) ->                   // <
                sprintf "(%s)<(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryLessEqual (left:Expression, right:Expression) ->                  // <=
                sprintf "(%s)<=(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryGreaterEqual (left:Expression, right:Expression ) ->              // >=
                sprintf "(%s)>=(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryGreaterThan (left:Expression, right:Expression  ) ->              // >
                sprintf "(%s)>(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryConjunction (left:Expression, right:Expression  ) ->              // &
                sprintf "(%s)&(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryDisjunction (left:Expression, right:Expression  ) ->              // |
                sprintf "(%s)|(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryIfAndOnlyIf (left:Expression, right:Expression  ) ->              // <=>
                sprintf "(%s)<=>(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.BinaryImplication (left:Expression, right:Expression  ) ->              // =>
                sprintf "(%s)=>(%s)" (this.ExportExpression left) (this.ExportExpression right)
            | Expression.TenaryIfThenElse (_if:Expression, _then:Expression, _else:Expression) ->  // ? :
                sprintf "(%s)?(%s):(%s)" (this.ExportExpression _if) (this.ExportExpression _then) (this.ExportExpression _else)
            // Functions
            | Expression.FunctionMin (exprs:Expression list) -> 
                let content = exprs |> List.map this.ExportExpression
                sprintf "min(%s)" (joinWithComma content)
            | Expression.FunctionMax (exprs:Expression list) -> 
                let content = exprs |> List.map this.ExportExpression
                sprintf "max(%s)" (joinWithComma content)
            | Expression.FunctionFloor (expr:Expression ) -> 
                sprintf "floor(%s)" (this.ExportExpression expr)
            | Expression.FunctionCeil (expr:Expression) -> 
                sprintf "ceil(%s)" (this.ExportExpression expr)
            | Expression.FunctionPow (_base:Expression, power:Expression) -> // Base^Power = Number
                sprintf "pow(%s,%s)" (this.ExportExpression _base) (this.ExportExpression power)
            | Expression.FunctionMod (dividend:Expression, divisor:Expression) ->  // Dividend % Divisor
                sprintf "mod(%s,%s)" (this.ExportExpression dividend) (this.ExportExpression divisor)
            | Expression.FunctionLog (_base:Expression, number:Expression) ->  // Log_Base(Number) = Power
                sprintf "log(%s,%s)" (this.ExportExpression number) (this.ExportExpression _base)




    ///////////////////////////
    // PROPERTIES
    ///////////////////////////

    member this.ExportBound (bound:Bound) : string =
        match bound with        
            | LessEqual (value:Constant) ->
                let value = this.ExportConstant value
                sprintf "<=%s" value
            | LessThan (value:Constant) ->
                let value = this.ExportConstant value
                sprintf "<%s" value
            | Equal (value:Constant) ->
                let value = this.ExportConstant value
                sprintf "=%s" value
            | GreaterEqual (value:Constant) ->
                let value = this.ExportConstant value
                sprintf ">=%s" value
            | GreaterThan (value:Constant) ->
                let value = this.ExportConstant value
                sprintf ">%s" value        

    member this.ExportQuery (query:Query) : string =
        match query with
            | Query.Deterministic -> "=?"
            | Query.IndeterministicMin -> "min=?"
            | Query.IndeterministicMax -> "max=?"
                            
    member this.ExportProperty (property : Property) : string =
        //TODO: Property and label with ""
        match property with
            | Property.Constant (constant:Constant) ->
                this.ExportConstant constant
            | Property.Variable (name:Identifier) ->
                this.ExportIdentifier name
            | Property.Formula (name:Identifier) ->
                this.ExportIdentifier name
            | Property.Label (name:Identifier) ->
                this.ExportIdentifier name
            | Property.Property (name:Identifier) -> //a property can also use the result (another (labeled) property as input)
                this.ExportIdentifier name
            // Properties with operators known from Propositional Logic
            | Property.UnaryNegation  (operand:Property) ->                                 // !
                sprintf "!(%s)" (this.ExportProperty operand)
            | Property.BinaryMultiplication (left:Property, right:Property) ->             // *
                sprintf "(%s)*(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryDivision (left:Property, right:Property) ->                   // / be cautious: Always performs floating point operation. 22/7 is 3.14... instead (3, even on integers
                sprintf "(%s)/(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryAddition (left:Property, right:Property) ->                   // +
                sprintf "(%s)+(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinarySubstraction (left:Property, right:Property) ->               // -
                sprintf "(%s)-(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryLessThan (left:Property, right:Property) ->                   // <
                sprintf "(%s)<(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryLessEqual (left:Property, right:Property) ->                  // <=
                sprintf "(%s)<=(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryGreaterEqual (left:Property, right:Property ) ->              // >=
                sprintf "(%s)>=(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryGreaterThan (left:Property, right:Property  ) ->              // >
                sprintf "(%s)>(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryConjunction (left:Property, right:Property  ) ->              // &
                sprintf "(%s)&(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryDisjunction (left:Property, right:Property  ) ->              // |
                sprintf "(%s)|(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryIfAndOnlyIf (left:Property, right:Property  ) ->              // <=>
                sprintf "(%s)<=>(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.BinaryImplication (left:Property, right:Property  ) ->              // =>
                sprintf "(%s)=>(%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.TenaryIfThenElse (_if:Property, _then:Property, _else:Property) ->  // ? :
                sprintf "(%s)?(%s):(%s)" (this.ExportProperty _if) (this.ExportProperty _then) (this.ExportProperty _else)
            // Functions
            | Property.FunctionMin (exprs:Property list) -> 
                let content = exprs |> List.map this.ExportProperty
                sprintf "min(%s)" (joinWithComma content)
            | Property.FunctionMax (exprs:Property list) -> 
                let content = exprs |> List.map this.ExportProperty
                sprintf "max(%s)" (joinWithComma content)
            | Property.FunctionFloor (expr:Property ) -> 
                sprintf "floor(%s)" (this.ExportProperty expr)
            | Property.FunctionCeil (expr:Property) -> 
                sprintf "ceil(%s)" (this.ExportProperty expr)
            | Property.FunctionPow (_base:Property, power:Property) -> // Base^Power = Number
                sprintf "pow(%s,%s)" (this.ExportProperty _base) (this.ExportProperty power)
            | Property.FunctionMod (dividend:Property, divisor:Property) ->  // Dividend % Divisor
                sprintf "mod(%s,%s)" (this.ExportProperty dividend) (this.ExportProperty divisor)
            | Property.FunctionLog (_base:Property, number:Property) ->  // Log_Base(Number) = Power
                sprintf "log(%s,%s)" (this.ExportProperty number) (this.ExportProperty _base)
            // Functions only usable in properties
            | Property.FunctionMultiAchievability (goal1:Property, goal2:Property) -> //Multi-Objective Property "achievability": Bool*Bool->Bool
                sprintf "multi(%s,%s)" (this.ExportProperty goal1) (this.ExportProperty goal1)
            | Property.FunctionMultiNumerical (searchBestValueFor:Property, constraints:(Property list)) -> //Multi-Objective Property "numerical": Double*(Bool list)->Double
                let constraints = constraints |> List.map (this.ExportProperty)
                sprintf "multi(%s,%s)" (this.ExportProperty searchBestValueFor) (joinWithComma constraints)
            | Property.FunctionMultiPareto (searchBestValueFor1:Property, searchBestValueFor2:Property) -> //Multi-Objective Property "Pareto": Double*Double->Void)
                sprintf "multi(%s,%s)" (this.ExportProperty searchBestValueFor1) (this.ExportProperty searchBestValueFor2)
            // LTL-Formula
            | Property.LtlUnaryNext (operand:Property) ->
                sprintf "X (%s)" (this.ExportProperty operand)
            | Property.LtlUnaryEventually (operand:Property) -> // Finally
                sprintf "F (%s)" (this.ExportProperty operand)
            | Property.LtlUnaryAlways (operand:Property) -> // Globally
                sprintf "G (%s)" (this.ExportProperty operand)
            | Property.LtlBinaryUntil (left:Property, right:Property) ->
                sprintf "(%s) U (%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.LtlBinaryWeakUntil (left:Property, right:Property) ->
                sprintf "(%s) W (%s)" (this.ExportProperty left) (this.ExportProperty right)
            | Property.LtlBinaryRelease (left:Property, right:Property) ->
                sprintf "(%s) R (%s)" (this.ExportProperty left) (this.ExportProperty right)
            // Probability            
            | ProbabilityAchievability (bound:Bound, operand:Property) ->
                sprintf "P%s [ %s ]" (this.ExportBound bound) (this.ExportProperty operand)
            | ProbabilityNumerical (query:Query,operand:Property) ->
                sprintf "P%s [ %s ]" (this.ExportQuery query) (this.ExportProperty operand)
             // Steady State
            | Property.SteadyStateAchievability (bound:Bound, operand:Property) ->
                sprintf "S%s [ %s ]" (this.ExportBound bound) (this.ExportProperty operand)
            | Property.SteadyStateNumerical (query:Query, operand:Property) ->
                sprintf "S%s [ %s ]" (this.ExportQuery query) (this.ExportProperty operand)
            //Reward
            | RewardReachabilityAchievability  (bound:Bound, operand:Property) ->
                sprintf "R%s [ F (%s) ]" (this.ExportBound bound) (this.ExportProperty operand)
            | RewardReachabilityNumerical (query:Query, operand:Property) ->
                sprintf "R%s [ F (%s) ]" (this.ExportQuery query) (this.ExportProperty operand)
            | RewardCumulativeAchievability  (bound:Bound,untilTimeStep:Property) ->
                sprintf "R%s [ C<=(%s) ]" (this.ExportBound bound) (this.ExportProperty untilTimeStep)
            | RewardCumulativeNumerical (query:Query,untilTimeStep:Property) ->
                sprintf "R%s [ C<=(%s) ]" (this.ExportQuery query) (this.ExportProperty untilTimeStep)
            | RewardInstantaneousAchievability (bound:Bound,inTimeStep:Property) ->
                sprintf "R%s [ I=(%s) ]" (this.ExportBound bound) (this.ExportProperty inTimeStep)
            | RewardInstantaneousNumerical (query:Query,inTimeStep:Property) ->
                sprintf "R%s [ I=(%s) ]" (this.ExportQuery query) (this.ExportProperty inTimeStep)
            | RewardSteadyStateAchievability (bound:Bound) ->
                sprintf "R%s [ S ]" (this.ExportBound bound)
            | RewardSteadyStateNumerical (query:Query) ->
                sprintf "R%s [ S ]" (this.ExportQuery query)
            //CTL
            | Property.ForAllPathsGlobally (operand:Property) ->
                sprintf "A [ G (%s)]" (this.ExportProperty operand)
            | Property.ForAllPathsFinally (operand:Property) ->
                sprintf "A [ F (%s)]" (this.ExportProperty operand)
            | Property.ExistsPathGlobally (operand:Property) ->
                sprintf "E [ G (%s)]" (this.ExportProperty operand)
            | Property.ExistsPathFinally (operand:Property) ->
                sprintf "E [ F (%s)]" (this.ExportProperty operand)
            // Filters
            | Property.FilterMin (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(min, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(min, %s)" (this.ExportProperty property)                
            | Property.FilterMax (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(max, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(max, %s)" (this.ExportProperty property)
            | Property.FilterArgmin (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(argmin, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(argmin, %s)" (this.ExportProperty property)
            | Property.FilterArgmax (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(argmax, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(argmax, %s)" (this.ExportProperty property)
            | Property.FilterCount (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(count, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(count, %s)" (this.ExportProperty property)
            | Property.FilterSum (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(sum, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(sum, %s)" (this.ExportProperty property)
            | Property.FilterAvg (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(avg, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(avg, %s)" (this.ExportProperty property)
            | Property.FilterFirst (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(first, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(first, %s)" (this.ExportProperty property)
            | Property.FilterRange (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(range, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(range, %s)" (this.ExportProperty property)
            | Property.FilterForall (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(forall, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(forall, %s)" (this.ExportProperty property)                

            | Property.FilterExists (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(exists, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(exists, %s)" (this.ExportProperty property)                

            | Property.FilterPrint (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(print, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(print, %s)" (this.ExportProperty property)                

            | Property.FilterPrintall (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(printall, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(printall, %s)" (this.ExportProperty property)                

            | Property.FilterState (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> sprintf "filter(state, %s, %s)" (this.ExportProperty property) (this.ExportProperty states)
                    | None -> sprintf "filter(state, %s)" (this.ExportProperty property)                

