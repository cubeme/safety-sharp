namespace SafetySharp.Tests.Modelchecking.Promela.PromelaAstToFileTests

module PromelaTests =
    let x=1

(*
TODO: port
    [TestFixture]
    public class EnumTests
    {
        [Test]
        public void SpinFound()
        {
            Spin.ExecuteSpin("-V").Should().Be(Spin.SpinResult.Success);
        }

        [Test]
        public void WriteEnumModelAndCheckParseability()
        {
            var filename = "Modelchecking\\Promela\\test1.pml";

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

            Spin.ExecuteSpin("-a " + filename).Should().Be(Spin.SpinResult.Success);
        }
    }

    [TestFixture]
    public class SeparatorTests
    {
        // Here we test, if (I) the correct number of separators
        // is written to a .pml-File and (II) the written file is parseable
        // http://spinroot.com/spin/Man/separators.html
        // http://spinroot.com/spin/Man/grammar.html

        private readonly Statement _simpleStatement1 = new ExpressionStatement(PromelaHelpers.ConstTrueExpression());
        private readonly Statement _simpleStatement2 = new SkipStatement();

        [Test]
        public void GuardedCommandClauseHasAnArrow()
        {
            var guardedCommandElseClause = new GuardedCommandElseClause(_simpleStatement1);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(guardedCommandElseClause);
            var output = fileWriter.CodeWriter.ToString().Trim();

            var arrowInTheMiddle = (output.IndexOf("->", System.StringComparison.Ordinal) > 0) && (output.IndexOf("->", System.StringComparison.Ordinal) < output.Length);

            arrowInTheMiddle.Should().BeTrue();
        }

        [Test]
        public void SemicolonsAreUsedCorrectlyInAGuardedCommandClause()
        {
            var guardedCommandElseClause = new GuardedCommandElseClause(_simpleStatement1);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(guardedCommandElseClause);
            var output = fileWriter.CodeWriter.ToString().Trim();

            var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
            var hasSemicolon = output.LastIndexOf(';') != -1;

            noSemicolonAtTheEnd.Should().BeTrue();
            hasSemicolon.Should().BeFalse();
        }

        [Test]
        public void SemicolonsAreUsedCorrectlyInASelectionAndASimpleStatementInASimpleBlock()
        {
            var elseClause = new GuardedCommandElseClause(_simpleStatement1);
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
        }

        [Test]
        public void SemicolonsAreUsedCorrectlyInOneSimpleStatementsInAProctype()
        {
            var simpleSequence = ImmutableArray<Statement>.Empty.Add(_simpleStatement1);
            var proctype = new Proctype(true, "System", simpleSequence);

            var fileWriter = new PromelaModelWriter(true);
            fileWriter.Visit(proctype);
            var output = fileWriter.CodeWriter.ToString().Trim();
            var noSemicolonAtTheEnd = output.LastIndexOf(';') != output.Length;
            var hasSemicolon = output.LastIndexOf(';') != -1;

            noSemicolonAtTheEnd.Should().BeTrue();
            hasSemicolon.Should().BeFalse();
        }

        [Test]
        public void SemicolonsAreUsedCorrectlyInTwoSimpleStatementsInAProctype()
        {
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
        }

        [Test]
        public void SemicolonsAreUsedCorrectlyInTwoSimpleStatementsInASimpleBlock()
        {
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
        }
    }
}

*)