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

namespace SafetySharp.Analysis.Modelchecking.Prism

module internal ExportPrismAstToFile =
    
    open SafetySharp.Models.SamToStringHelpers
    
    let indent0ElementWithNewLine<'a> (writer:'a->AstToStringStateFunction) (elem:'a) = 
        (writer elem) >>= (append "\n")

    let indent1ElementWithNewLine<'a> (writer:'a->AstToStringStateFunction) (elem:'a) = 
        (append "\t") >>= writer elem >>= (append "\n")

    let inParenthesis<'a> (writer:'a->AstToStringStateFunction) (elem:'a) = 
        (append "(") >>= writer elem >>= (append ")")

    // member e(.*) : string =
    // let e$1 : AstToStringStateFunction =

    let cultureInfo = System.Globalization.CultureInfo.InvariantCulture

    let exportConstant (constant : Constant) : AstToStringStateFunction = 
        match constant with
            | Integer (_int) -> append (_int.ToString())
            | Double (_double) -> append (_double.ToString(cultureInfo))
            | Boolean (_bool) -> if _bool then append "true" else append "false"
    
    let exportIdentifier (identifier : Identifier) : AstToStringStateFunction = 
        append (identifier.Name)

    let exportLabel (label : Label) : AstToStringStateFunction = 
        append (sprintf "\"%s\"" label.Name)

    let exportDefactoType (defactoType:DefactoType) : AstToStringStateFunction =
        match defactoType with
            | DefactoType.Bool -> append "bool"
            | DefactoType.Int -> append "int"
            | DefactoType.Double -> append "double"
                                        
    let rec exportExpression (expression : Expression) : AstToStringStateFunction =
        match expression with
            | Expression.Constant (constant:Constant) ->
                exportConstant constant
            | Expression.Variable (name:Identifier) ->
                exportIdentifier name
            | Expression.Formula (name:Identifier) ->
                exportIdentifier name
            // Expressions with operators known from Propositional Logic
            | Expression.UnaryNot  (operand:Expression) ->                                 // !
                mprintf1 "!(%s)" (exportExpression operand)
            | Expression.BinaryMultiplication (left:Expression, right:Expression) ->             // *
                mprintf2 "(%s)*(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryDivision (left:Expression, right:Expression) ->                   // / be cautious: Always performs floating point operation. 22/7 is 3.14... instead (3, even on integers
                mprintf2 "(%s)/(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryAddition (left:Expression, right:Expression) ->                   // +
                mprintf2 "(%s)+(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinarySubstraction (left:Expression, right:Expression) ->               // -
                mprintf2 "(%s)-(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryLessThan (left:Expression, right:Expression) ->                   // <
                mprintf2 "(%s)<(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryLessEqual (left:Expression, right:Expression) ->                  // <=
                mprintf2 "(%s)<=(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryGreaterEqual (left:Expression, right:Expression ) ->              // >=
                mprintf2 "(%s)>=(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryGreaterThan (left:Expression, right:Expression  ) ->              // >
                mprintf2 "(%s)>(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryConjunction (left:Expression, right:Expression  ) ->              // &
                mprintf2 "(%s)&(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryDisjunction (left:Expression, right:Expression  ) ->              // |
                mprintf2 "(%s)|(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryIfAndOnlyIf (left:Expression, right:Expression  ) ->              // <=>
                mprintf2 "(%s)<=>(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryImplication (left:Expression, right:Expression  ) ->              // =>
                mprintf2 "(%s)=>(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryEquals (left:Expression, right:Expression  ) ->                   // =
                mprintf2 "(%s)=(%s)" (exportExpression left) (exportExpression right)
            | Expression.BinaryNotEquals(left:Expression, right:Expression  ) ->                 // !=
                mprintf2 "(%s)!=(%s)" (exportExpression left) (exportExpression right)
            | Expression.TenaryIfThenElse (_if:Expression, _then:Expression, _else:Expression) ->  // ? :
                mprintf3 "(%s)?(%s):(%s)" (exportExpression _if) (exportExpression _then) (exportExpression _else)
            // Functions
            | Expression.FunctionMin (exprs:Expression list) -> 
                mprintf1 "min(%s)" (foreachWithSep exprs exportExpression (append  ","))
            | Expression.FunctionMax (exprs:Expression list) -> 
                mprintf1 "max(%s)" (foreachWithSep exprs exportExpression (append  ","))
            | Expression.FunctionFloor (expr:Expression ) -> 
                mprintf1 "floor(%s)" (exportExpression expr)
            | Expression.FunctionCeil (expr:Expression) -> 
                mprintf1 "ceil(%s)" (exportExpression expr)
            | Expression.FunctionPow (_base:Expression, power:Expression) -> // Base^Power = Number
                mprintf2 "pow(%s,%s)" (exportExpression _base) (exportExpression power)
            | Expression.FunctionMod (dividend:Expression, divisor:Expression) ->  // Dividend % Divisor
                mprintf2 "mod(%s,%s)" (exportExpression dividend) (exportExpression divisor)
            | Expression.FunctionLog (_base:Expression, number:Expression) ->  // Log_Base(Number) = Power
                mprintf2 "log(%s,%s)" (exportExpression number) (exportExpression _base)
                
    let exportVariableDeclarationType (variableDeclarationType:VariableDeclarationType) : AstToStringStateFunction =
        match variableDeclarationType with
            | VariableDeclarationType.Bool ->
                append "bool"
            | VariableDeclarationType.IntRange (_from:Expression, _to:Expression) ->
                append "[" >>=
                (exportExpression _from) >>=
                append ".." >>=
                (exportExpression _to) >>=
                append "]"
            | VariableDeclarationType.Int ->
                append "int"
            | VariableDeclarationType.Clock ->
                append "clock"

    let exportVariableDeclaration (variableDeclaration:VariableDeclaration) : AstToStringStateFunction =
        let _name = exportIdentifier variableDeclaration.Name
        let _type = exportVariableDeclarationType variableDeclaration.Type
        let _initValue =
            match variableDeclaration.InitialValue with
                | Some(expr) -> mprintf1 " init %s" (exportExpression expr)
                | None -> append ""
        mprintf3 "%s : %s%s;" _name _type _initValue

    let exportConstantDeclaration (constantDeclaration:ConstantDeclaration) : AstToStringStateFunction =
        let _type = exportDefactoType constantDeclaration.Type
        let _name = exportIdentifier constantDeclaration.Name
        let _init = exportExpression constantDeclaration.Value
        mprintf3 "const %s %s = %s;" _type _name _init

    let exportCommand (command:Command) : AstToStringStateFunction =
        let exportDeterministicUpdateOfVariables (update:DeterministicUpdateOfVariables) : AstToStringStateFunction =
            if update = [] then
                append "true"
            else
                //something like (x1'=x1)&(x2'=x2)
                foreachWithSep update (fun (targetVariable,expr) -> mprintf2 "(%s'=%s)" (exportIdentifier targetVariable) (exportExpression expr)) (append "&")
        let exportQuantifiedUpdateOfVariables (update:QuantifiedUpdateOfVariables) : AstToStringStateFunction =
            //something like 0.8:(x1'=x1)&(x2'=x2) + 0.2:(x1'=0)&(x2'=1)
            if update = [] then
                append "1.0:true"
            else
                foreachWithSep update (fun (associateProbability,deterministicUpdate) ->
                                            let associateProbability = exportExpression associateProbability
                                            let deterministicUpdate = exportDeterministicUpdateOfVariables deterministicUpdate
                                            mprintf2 "(%s):%s" associateProbability deterministicUpdate
                                       ) 
                                       (append " + ")
        let exportAction (action:CommandAction) : AstToStringStateFunction =
            match action with
                | CommandAction.NoActionLabel -> append ""
                | CommandAction.Synchronized(actionLabel) -> (exportIdentifier actionLabel) //actionLabel is in fact an identifier, there are no quotation marks necessary
        let actionForSynchronization = (exportAction command.Action)
        let guard = exportExpression command.Guard
        let updates = exportQuantifiedUpdateOfVariables command.QuantifiedUpdateOfVariables
        mprintf3 "[%s] %s -> %s;" actionForSynchronization guard updates

    let exportModule (_module:Module) : AstToStringStateFunction =
        match _module with
            | Module.ModulePta(name:Identifier, variables:(VariableDeclaration list), invariant:Expression, commands:(Command list)) ->
                let name = exportIdentifier name
                let variables = foreach variables (indent1ElementWithNewLine exportVariableDeclaration)
                let invariant = exportExpression invariant
                let commands = foreach commands (indent1ElementWithNewLine exportCommand)
                mprintf4 "module %s\n%s\ninvariant\n\t%s\nendinvariant\n%sendmodule\n" name variables invariant commands
            | Module.ModuleRenaming(name:Identifier, cloneOf:Identifier, renamings:((Identifier*Identifier) list)) ->
                let name = exportIdentifier name
                let cloneOf = exportIdentifier cloneOf
                let renamePair (variableToReplace:Identifier,replacedBy:Identifier) : AstToStringStateFunction =
                    mprintf2 "%s=%s" (exportIdentifier variableToReplace) (exportIdentifier replacedBy) 
                let renamings = foreachWithSep renamings renamePair (append ",")
                mprintf3 "module %s = %s [ %s ] endmodule\n" name cloneOf renamings
            | Module.Module(name:Identifier, variables:(VariableDeclaration list), commands:(Command list)) ->
                let name = exportIdentifier name
                let variables = foreach variables (indent1ElementWithNewLine exportVariableDeclaration)
                let commands = foreach commands (indent1ElementWithNewLine exportCommand)
                mprintf3 "module %s\n%s%sendmodule\n" name variables commands


    let exportFormula (formula:Formula) : AstToStringStateFunction =
        mprintf2 "formula %s = %s;" (exportIdentifier formula.Name) (exportExpression formula.Formula)
        
    let exportLabeledExpression (labeledExpression:LabeledExpression) : AstToStringStateFunction =
        mprintf2 "label %s = %s;" (exportLabel labeledExpression.Label) (exportExpression labeledExpression.Expression)

    let exportRewardStructure (rewardStructure:RewardStructure) : AstToStringStateFunction =
        let exportReward(reward:Reward) : AstToStringStateFunction =
            match reward with
                | StateReward (guard:Expression, reward:Expression) ->
                    mprintf2 "%s : %s;" (exportExpression guard) (exportExpression reward)
                | TransitionReward (action:ActionLabel, guard:Expression, reward:Expression) ->
                    mprintf3 "[%s] %s : %s;" (exportIdentifier action) (exportExpression guard) (exportExpression reward)
        let name = if rewardStructure.Label.IsNone then append "" else (append " ")  >>= (exportLabel rewardStructure.Label.Value)
        let rewards = foreach (rewardStructure.Rewards) (indent1ElementWithNewLine exportReward)
        mprintf2 "rewards%s\n%sendrewards\n" name rewards

    let rec exportProcessAlgebraicExpression (processAlgebraicExpression:ProcessAlgebraicExpression) : AstToStringStateFunction =
        match processAlgebraicExpression with            
            | Module (name:Identifier) ->
                exportIdentifier name
            | OnActions (ms:ProcessAlgebraicExpression list) ->
                // M1 || M2
                foreachWithSep ms (inParenthesis exportProcessAlgebraicExpression) (append "||")
            | Asynchronous (ms:ProcessAlgebraicExpression list) ->
                // M1 ||| M2
                foreachWithSep ms (inParenthesis exportProcessAlgebraicExpression) (append "|||")
            | OnSomeActions (m1:ProcessAlgebraicExpression, m2:ProcessAlgebraicExpression, actions:(ActionLabel list)) ->
                // M1 |[a,b,...]| M2
                let actions = foreachWithSep actions exportIdentifier (append ",")
                mprintf3 "%s |[%s]| %s" (exportProcessAlgebraicExpression m1) actions (exportProcessAlgebraicExpression m2)
            | HideActions (m:ProcessAlgebraicExpression, actions:(ActionLabel list)) ->
                // M / {a,b,...}
                let actions = foreachWithSep actions exportIdentifier (append ",")
                mprintf2 "%s / {%s}" (exportProcessAlgebraicExpression m) actions
            | RenameActions (m:ProcessAlgebraicExpression, renamings:((ActionLabel*ActionLabel) list)) ->
                // M {a<-b,c<-d}
                let renamePair (_from:ActionLabel,_to:ActionLabel) : AstToStringStateFunction =
                    mprintf2 "%s<-%s" (exportIdentifier _from) (exportIdentifier _to)
                let renamings = foreachWithSep renamings renamePair (append ",")
                mprintf2 "%s / {%s}" (exportProcessAlgebraicExpression m) renamings

    let exportPrismModel (prismModel:PrismModel) : AstToStringStateFunction =
        let exportModelType (modelType:ModelType) : AstToStringStateFunction =
            match modelType with
                | MDP -> append "mdp"
                | DTMC -> append "dtmc"
                | CTMC -> append "ctmc"
                | PTA -> append "pta"
        let modelType = exportModelType prismModel.ModelType
        let constants = foreach prismModel.Constants (indent0ElementWithNewLine exportConstantDeclaration)
        let initModule =
            match prismModel.InitModule with
                | None -> append ""
                | Some(expr) -> mprintf1 "init\n\t%s\nendinit\n\n" (exportExpression expr)
        let globalVariables = foreach prismModel.GlobalVariables (indent0ElementWithNewLine (fun elem -> (append "global ") >>= (exportVariableDeclaration elem)))
        let formulas = foreachWithSep prismModel.Formulas exportFormula (append "\n")
        let modules = foreachWithSep prismModel.Modules exportModule (append "\n")
        let labels = foreachWithSep prismModel.Labels exportLabeledExpression (append "\n")
        let rewards = foreachWithSep prismModel.Rewards exportRewardStructure (append "\n")
        let parallelComposition =             
            match prismModel.ParallelComposition with
                | None -> append ""
                | Some(parallelExpr) -> exportProcessAlgebraicExpression parallelExpr
        
        modelType >>= newParagraph >>=
          initModule >>= 
          constants  >>=
          globalVariables  >>=
          formulas  >>= newLine >>=
          modules  >>= newLine >>=
          labels  >>= newLine >>=
          rewards  >>= newLine >>=
          parallelComposition


    ///////////////////////////
    // PROPERTIES
    ///////////////////////////

    let exportBound (bound:Bound) : AstToStringStateFunction =
        match bound with        
            | Bound.LessEqual (value:Constant) ->
                let value = exportConstant value
                mprintf1 "<=%s" value
            | Bound.LessThan (value:Constant) ->
                let value = exportConstant value
                mprintf1 "<%s" value
            | Bound.Equal (value:Constant) ->
                let value = exportConstant value
                mprintf1 "=%s" value
            | Bound.GreaterEqual (value:Constant) ->
                let value = exportConstant value
                mprintf1 ">=%s" value
            | Bound.GreaterThan (value:Constant) ->
                let value = exportConstant value
                mprintf1 ">%s" value        

    let exportPathBound (bound:PathBound option) : AstToStringStateFunction =
        match bound with
            | None -> append ""
            | Some(bound) ->
                match bound with
                    | PathBound.LessEqual (_to:Constant) -> mprintf1 "<=%s" (exportConstant _to)
                    | PathBound.LessThan (_to:Constant) -> mprintf1 "<%s" (exportConstant _to)
                    | PathBound.Interval (_from:Constant,_to:Constant) -> mprintf2 "[%s,%s]" (exportConstant _from) (exportConstant _to)
                    | PathBound.GreaterEqual (_from:Constant) -> mprintf1 ">=%s" (exportConstant _from)
                    | PathBound.GreaterThan (_from:Constant) -> mprintf1 ">%s" (exportConstant _from)

    let exportQuery (query:Query) : AstToStringStateFunction =
        match query with
            | Query.Deterministic -> append "=?"
            | Query.IndeterministicMin -> append "min=?"
            | Query.IndeterministicMax -> append "max=?"
                            
    let rec exportProperty (property : Property) : AstToStringStateFunction =
        // helpers
        let exportRewardLabel (rewardLabel:(Label option)) :AstToStringStateFunction =
            match rewardLabel with
                | None -> append ""
                | Some(label) -> mprintf1 "{%s}" (exportLabel label)
        // actual function
        match property with
            | Property.Constant (constant:Constant) ->
                exportConstant constant
            | Property.Variable (name:Identifier) ->
                exportIdentifier name
            | Property.Formula (name:Identifier) ->
                exportIdentifier name
            | Property.Label (label:Label) ->
                exportLabel label
            | Property.Property (name:Identifier) -> //a property can also use the result (another (labeled) property as input)
                exportIdentifier name
            // Properties with operators known from Propositional Logic
            | Property.UnaryNegation  (operand:Property) ->                                 // !
                mprintf1 "!(%s)" (exportProperty operand)
            | Property.BinaryMultiplication (left:Property, right:Property) ->             // *
                mprintf2 "(%s)*(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryDivision (left:Property, right:Property) ->                   // / be cautious: Always performs floating point operation. 22/7 is 3.14... instead (3, even on integers
                mprintf2 "(%s)/(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryAddition (left:Property, right:Property) ->                   // +
                mprintf2 "(%s)+(%s)" (exportProperty left) (exportProperty right)
            | Property.BinarySubstraction (left:Property, right:Property) ->               // -
                mprintf2 "(%s)-(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryLessThan (left:Property, right:Property) ->                   // <
                mprintf2 "(%s)<(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryLessEqual (left:Property, right:Property) ->                  // <=
                mprintf2 "(%s)<=(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryGreaterEqual (left:Property, right:Property ) ->              // >=
                mprintf2 "(%s)>=(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryGreaterThan (left:Property, right:Property  ) ->              // >
                mprintf2 "(%s)>(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryConjunction (left:Property, right:Property  ) ->              // &
                mprintf2 "(%s)&(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryDisjunction (left:Property, right:Property  ) ->              // |
                mprintf2 "(%s)|(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryIfAndOnlyIf (left:Property, right:Property  ) ->              // <=>
                mprintf2 "(%s)<=>(%s)" (exportProperty left) (exportProperty right)
            | Property.BinaryImplication (left:Property, right:Property  ) ->              // =>
                mprintf2 "(%s)=>(%s)" (exportProperty left) (exportProperty right)
            | Property.TenaryIfThenElse (_if:Property, _then:Property, _else:Property) ->  // ? :
                mprintf3 "(%s)?(%s):(%s)" (exportProperty _if) (exportProperty _then) (exportProperty _else)
            // Functions
            | Property.FunctionMin (exprs:Property list) -> 
                mprintf1 "min(%s)" (foreachWithSep exprs exportProperty (append ","))
            | Property.FunctionMax (exprs:Property list) -> 
                mprintf1 "max(%s)" (foreachWithSep exprs exportProperty (append ","))
            | Property.FunctionFloor (expr:Property ) -> 
                mprintf1 "floor(%s)" (exportProperty expr)
            | Property.FunctionCeil (expr:Property) -> 
                mprintf1 "ceil(%s)" (exportProperty expr)
            | Property.FunctionPow (_base:Property, power:Property) -> // Base^Power = Number
                mprintf2 "pow(%s,%s)" (exportProperty _base) (exportProperty power)
            | Property.FunctionMod (dividend:Property, divisor:Property) ->  // Dividend % Divisor
                mprintf2 "mod(%s,%s)" (exportProperty dividend) (exportProperty divisor)
            | Property.FunctionLog (_base:Property, number:Property) ->  // Log_Base(Number) = Power
                mprintf2 "log(%s,%s)" (exportProperty number) (exportProperty _base)
            // Functions only usable in properties
            | Property.FunctionMultiAchievability (goal1:Property, goal2:Property) -> //Multi-Objective Property "achievability": Bool*Bool->Bool
                mprintf2 "multi(%s,%s)" (exportProperty goal1) (exportProperty goal2)
            | Property.FunctionMultiNumerical (searchBestValueFor:Property, constraints:(Property list)) -> //Multi-Objective Property "numerical": Double*(Bool list)->Double
                mprintf2 "multi(%s,%s)" (exportProperty searchBestValueFor) (foreachWithSep constraints exportProperty (append ","))
            | Property.FunctionMultiPareto (searchBestValueFor1:Property, searchBestValueFor2:Property) -> //Multi-Objective Property "Pareto": Double*Double->Void)
                mprintf2 "multi(%s,%s)" (exportProperty searchBestValueFor1) (exportProperty searchBestValueFor2)
            // LTL-Formula
            | Property.LtlUnaryNext (operand:Property) ->
                mprintf1 "X (%s)" (exportProperty operand)
            | LtlUnaryInTimeInstant (timeInstant:Property, operand:Property) ->
                mprintf2 "F=%s (%s)" (exportProperty timeInstant) (exportProperty operand)
            | Property.LtlUnaryEventually (withinSteps:(PathBound option),operand:Property) -> // Finally
                mprintf2 "F%s (%s)" (exportPathBound withinSteps) (exportProperty operand)
            | Property.LtlUnaryAlways (withinSteps:(PathBound option),operand:Property) -> // Globally
                mprintf2 "G%s (%s)"  (exportPathBound withinSteps) (exportProperty operand)
            | Property.LtlBinaryUntil (withinSteps:(PathBound option),left:Property, right:Property) ->
                mprintf3 "(%s) U%s (%s)" (exportProperty left)  (exportPathBound withinSteps) (exportProperty right)
            | Property.LtlBinaryWeakUntil (withinSteps:(PathBound option),left:Property, right:Property) ->
                mprintf3 "(%s) W%s (%s)" (exportProperty left) (exportPathBound withinSteps) (exportProperty right)
            | Property.LtlBinaryRelease (withinSteps:(PathBound option),left:Property, right:Property) ->
                mprintf3 "(%s) R%s (%s)" (exportProperty left) (exportPathBound withinSteps) (exportProperty right)
            // Probability            
            | ProbabilityAchievability (bound:Bound, operand:Property) ->
                mprintf2 "P%s [ %s ]" (exportBound bound) (exportProperty operand)
            | ProbabilityNumerical (query:Query,operand:Property) ->
                mprintf2 "P%s [ %s ]" (exportQuery query) (exportProperty operand)
             // Steady State
            | Property.SteadyStateAchievability (bound:Bound, operand:Property) ->
                mprintf2 "S%s [ %s ]" (exportBound bound) (exportProperty operand)
            | Property.SteadyStateNumerical (query:Query, operand:Property) ->
                mprintf2 "S%s [ %s ]" (exportQuery query) (exportProperty operand)
            //Reward
            | RewardReachabilityAchievability  (rewardLabel:(Label option),bound:Bound, operand:Property) ->
                mprintf3 "R%s%s [ F (%s) ]" (exportRewardLabel rewardLabel) (exportBound bound) (exportProperty operand)
            | RewardReachabilityNumerical (rewardLabel:(Label option),query:Query, operand:Property) ->
                mprintf3 "R%s%s [ F (%s) ]" (exportRewardLabel rewardLabel) (exportQuery query) (exportProperty operand)
            | RewardCumulativeAchievability  (rewardLabel:(Label option),bound:Bound,untilTimeStep:Property) ->
                mprintf3 "R%s%s [ C<=(%s) ]" (exportRewardLabel rewardLabel) (exportBound bound) (exportProperty untilTimeStep)
            | RewardCumulativeNumerical (rewardLabel:(Label option),query:Query,untilTimeStep:Property) ->
                mprintf3 "R%s%s [ C<=(%s) ]" (exportRewardLabel rewardLabel) (exportQuery query) (exportProperty untilTimeStep)
            | RewardInstantaneousAchievability (rewardLabel:(Label option),bound:Bound,inTimeStep:Property) ->
                mprintf3 "R%s%s [ I=(%s) ]" (exportRewardLabel rewardLabel) (exportBound bound) (exportProperty inTimeStep)
            | RewardInstantaneousNumerical (rewardLabel:(Label option),query:Query,inTimeStep:Property) ->
                mprintf3 "R%s%s [ I=(%s) ]" (exportRewardLabel rewardLabel) (exportQuery query) (exportProperty inTimeStep)
            | RewardSteadyStateAchievability (rewardLabel:(Label option),bound:Bound) ->
                mprintf2 "R%s%s [ S ]" (exportRewardLabel rewardLabel) (exportBound bound)
            | RewardSteadyStateNumerical (rewardLabel:(Label option),query:Query) ->
                mprintf2 "R%s%s [ S ]" (exportRewardLabel rewardLabel) (exportQuery query)
            //CTL
            | Property.ForAllPathsGlobally (operand:Property) ->
                mprintf1 "A [ G (%s)]" (exportProperty operand)
            | Property.ForAllPathsFinally (operand:Property) ->
                mprintf1 "A [ F (%s)]" (exportProperty operand)
            | Property.ExistsPathGlobally (operand:Property) ->
                mprintf1 "E [ G (%s)]" (exportProperty operand)
            | Property.ExistsPathFinally (operand:Property) ->
                mprintf1 "E [ F (%s)]" (exportProperty operand)
            // Filters
            | Property.FilterMin (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(min, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(min, %s)" (exportProperty property)                
            | Property.FilterMax (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(max, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(max, %s)" (exportProperty property)
            | Property.FilterArgmin (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(argmin, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(argmin, %s)" (exportProperty property)
            | Property.FilterArgmax (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(argmax, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(argmax, %s)" (exportProperty property)
            | Property.FilterCount (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(count, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(count, %s)" (exportProperty property)
            | Property.FilterSum (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(sum, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(sum, %s)" (exportProperty property)
            | Property.FilterAvg (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(avg, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(avg, %s)" (exportProperty property)
            | Property.FilterFirst (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(first, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(first, %s)" (exportProperty property)
            | Property.FilterRange (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(range, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(range, %s)" (exportProperty property)
            | Property.FilterForall (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(forall, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(forall, %s)" (exportProperty property)                

            | Property.FilterExists (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(exists, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(exists, %s)" (exportProperty property)                

            | Property.FilterPrint (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(print, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(print, %s)" (exportProperty property)                

            | Property.FilterPrintall (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(printall, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(printall, %s)" (exportProperty property)                

            | Property.FilterState (property:Property, states:Property option) ->
                match states with
                    | Some(states) -> mprintf2 "filter(state, %s, %s)" (exportProperty property) (exportProperty states)
                    | None -> mprintf1 "filter(state, %s)" (exportProperty property)                

                    
    open SafetySharp.Workflow


    let workflow () 
            : ExogenousWorkflowFunction<PrismModel,string> = workflow {            
        let! model = getState ()
        let exportedModelState = exportPrismModel model AstToStringState.initial
        do! updateState (exportedModelState.ToString())
    }