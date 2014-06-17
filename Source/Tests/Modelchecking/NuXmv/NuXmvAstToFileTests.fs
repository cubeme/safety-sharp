module NuXmvTests

(*
[Test]
        public void MainModuleTest()
        {
            var mainModuleIdentifier = new Identifier("main");
            var mainModuleElements = ImmutableArray<ModuleElement>.Empty;
            var mainModule = new ModuleDeclaration(mainModuleIdentifier, ImmutableArray<Identifier>.Empty, mainModuleElements);

            var fileWriter = new NuXmvModelWriter(true);
            fileWriter.Visit(mainModule);
            var output = fileWriter.CodeWriter.ToString().Trim();

            
            output.Contains("MODULE main").Should().BeTrue();
        }

*)