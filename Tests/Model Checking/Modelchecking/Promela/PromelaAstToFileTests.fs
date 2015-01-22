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

namespace SafetySharp.Tests.Modelchecking.Promela.PromelaAstToFileTests

open NUnit.Framework
open SafetySharp.Internal.Modelchecking.PromelaSpin
open PromelaAstHelpers
open SafetySharp.Tests

[<TestFixture>]
module EnumTests =

    [<Test>]
    let ``spin found`` () =
        //Spin.ExecuteSpin("-V").Should().Be(Spin.SpinResult.Success);
        ()

    [<Test>]
    let ``write enum model and check parseability`` () =
        (*var filename = "Modelchecking\\Promela\\test1.pml";

            var expr_false = new BooleanLiteral(false);
            var expr_true = new BooleanLiteral(false);

            var stmnt_declvarx = new DeclarationStatement(PromelaTypeName.Bool, "x", 0, expr_false);
            var ref_varX = new VariableReferenceExpression("x", null, null);
            var stmnt_assignTrueToVarx = new AssignmentStatement(ref_varX, expr_true);

            var code = ImmutableArray.Create<Statement>().Add(stmnt_declvarx).Add(stmnt_assignTrueToVarx);

            var testProcType = new Proctype(true, "TestProcType", code);

            var fileWriter = new PromelaModelWriter();
            fileWriter.Visit(testProcType);

            fileWriter.CodeWriter.WriteToFile(filename);

            Spin.ExecuteSpin("-a " + filename).Should().Be(Spin.SpinResult.Success);*)
        ()

[<TestFixture>]
module SeparatorTests =    
    // Here we test, if (I) the correct number of separators
    // is written to a .pml-File and (II) the written file is parseable
    // http://spinroot.com/spin/Man/separators.html
    // http://spinroot.com/spin/Man/grammar.html
    
    let private astToFile = ExportPromelaAstToFile()
    let private indent = 0

    let private simpleStatement1 = Stmnt.ExprStmnt(Expr.AnyExpr(AnyExpr.Const(Const.True)))
    let private simpleStatement2 = Stmnt.ExprStmnt(Expr.AnyExpr(AnyExpr.Const(Const.Skip)))
    let private elseStatement = Stmnt.ElseStmnt
    
    let private option1Sequence = statementsToSequence [simpleStatement1;simpleStatement2]
    let private option2Sequence = statementsToSequence [elseStatement;simpleStatement2]
    
    let private simpleGuardedCommand1 = Stmnt.IfStmnt(Options.Options([option1Sequence]))
    let private simpleGuardedCommand2 = Stmnt.IfStmnt(Options.Options([option1Sequence;option2Sequence]))
    
    [<Test>]
    let ``simple guarded command clause has _one_ separator in the middle`` () =
        let output = astToFile.ExportStmnt indent simpleGuardedCommand1
        let hasSemicolonInTheMiddle = (output.IndexOf(";", System.StringComparison.Ordinal) > 0) && (output.IndexOf(";", System.StringComparison.Ordinal) < output.Length)
        let noSemicolonAtTheEnd = output.LastIndexOf(';') <> output.Length
        let onlyOneSemicolon = output.IndexOf(";", System.StringComparison.Ordinal) = output.LastIndexOf(";", System.StringComparison.Ordinal)
        hasSemicolonInTheMiddle =? true
        noSemicolonAtTheEnd =? true
        onlyOneSemicolon =? true
       
    (*
    To port
    [<Test>]
    let ``SemicolonsAreUsedCorrectlyInASelectionAndASimpleStatementInASimpleBlock`` () =
        //var guardedCommandElseClause = new GuardedCommandElseClause(_simpleStatement1);
        //var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
        //var hasSemicolon = output.LastIndexOf(';') != -1;
        //noSemicolonAtTheEnd.Should().BeTrue();
        //hasSemicolon.Should().BeFalse();var elseClause = new GuardedCommandElseClause(_simpleStatement1);
            var selection = new GuardedCommandSelectionStatement(ImmutableArray<GuardedCommandClause>.Empty.Add(elseClause));
            var sequence = ImmutableArray<Statement>.Empty.Add(selection).Add(_simpleStatement2);
            var block = new SimpleBlockStatement(sequence);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(block);
            var output = fileWriter.CodeWriter.ToString().Trim();
            var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
            var onlyOneUseOfSemicolon = output.LastIndexOf(';') == output.IndexOf(';');

            var stringInBrackets = output.Substring(output.IndexOf('{'));
            stringInBrackets = stringInBrackets.Remove(stringInBrackets.IndexOf('}'));
            var noSemicolonBeforeBracketAtTheEnd = stringInBrackets.LastIndexOf(';') != stringInBrackets.Length;
            var semiColonInTheMiddle = (stringInBrackets.IndexOf(';') > 0) && (stringInBrackets.IndexOf(';') < stringInBrackets.Length);

            noSemicolonAtTheEnd.Should().BeTrue();
            onlyOneUseOfSemicolon.Should().BeTrue();
            noSemicolonBeforeBracketAtTheEnd.Should().BeTrue();
            semiColonInTheMiddle.Should().BeTrue();
        ()

    [<Test>]
    let ``SemicolonsAreUsedCorrectlyInOneSimpleStatementsInAProctype`` () =
        var simpleSequence = ImmutableArray<Statement>.Empty.Add(_simpleStatement1);
            var proctype = new Proctype(true, "System", simpleSequence);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(proctype);
            var output = fileWriter.CodeWriter.ToString().Trim();
            var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
            var hasSemicolon = output.LastIndexOf(';') != -1;

            noSemicolonAtTheEnd.Should().BeTrue();
            hasSemicolon.Should().BeFalse();
        ()

    [<Test>]
    let ``SemicolonsAreUsedCorrectlyInTwoSimpleStatementsInAProctype`` () =
            var simpleSequence = ImmutableArray<Statement>.Empty.Add(_simpleStatement1).Add(_simpleStatement2);
            var proctype = new Proctype(true, "System", simpleSequence);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(proctype);
            var output = fileWriter.CodeWriter.ToString().Trim();
            var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
            var onlyOneUseOfSemicolon = output.LastIndexOf(';') == output.IndexOf(';');
            var semiColonInTheMiddle = (output.IndexOf(';') > 0) && (output.IndexOf(';') < output.Length);
            noSemicolonAtTheEnd.Should().BeTrue();
            onlyOneUseOfSemicolon.Should().BeTrue();
            semiColonInTheMiddle.Should().BeTrue();
        ()

    [<Test>]
    let ``SemicolonsAreUsedCorrectlyInTwoSimpleStatementsInASimpleBlock`` () =
        
            var simpleSequence = ImmutableArray<Statement>.Empty.Add(_simpleStatement1).Add(_simpleStatement2);
            var block = new SimpleBlockStatement(simpleSequence);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(block);
            var output = fileWriter.CodeWriter.ToString().Trim();
            var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
            var onlyOneUseOfSemicolon = output.LastIndexOf(';') == output.IndexOf(';');

            var stringInBrackets = output.Substring(output.IndexOf('{'));
            stringInBrackets = stringInBrackets.Remove(stringInBrackets.IndexOf('}'));
            var noSemicolonBeforeBracketAtTheEnd = stringInBrackets.LastIndexOf(';') != stringInBrackets.Length;
            var semiColonInTheMiddle = (stringInBrackets.IndexOf(';') > 0) && (stringInBrackets.IndexOf(';') < stringInBrackets.Length);

            noSemicolonAtTheEnd.Should().BeTrue();
            onlyOneUseOfSemicolon.Should().BeTrue();
            noSemicolonBeforeBracketAtTheEnd.Should().BeTrue();
            semiColonInTheMiddle.Should().BeTrue();
        ()*)

