namespace SafetySharp.Tests.Modelchecking.Promela.PromelaTransformMetamodelTests

open NUnit.Framework
open Swensen.Unquote
open SafetySharp.Tests.Modelchecking

open SafetySharp.Modelchecking.PromelaSpin

[<TestFixture>]
module TestCase1ToPromelaTests =
    open TestCase1

    [<Test>]
    let ``transforms model`` () =
        let modelTransformer = MetamodelToPromela (testCase1Configuration)
        let promelaCode = modelTransformer.transformConfiguration
        ()
