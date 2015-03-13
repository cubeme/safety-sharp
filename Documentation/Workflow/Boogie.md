# The boogie pipeline to verify SafetySharp models

## Requirements (Windows)

* Z3 from http://z3.codeplex.com/
* Boogie from http://boogie.codeplex.com/. Note: The version "Boogie and Dafny, 22 Oct 2012" is to old and does not work with Z3 4.3.2. You might need to download the current branch from http://boogie.codeplex.com/SourceControl/latest and compile a current version of boogie.

## Workflow from SCM to Boogie



```
do! ScmWorkflow.setPlainModelState scm
do! SafetySharp.Models.ScmRewriterFlattenModel.flattenModel
... //TODO
do! SafetySharp.Analysis.VerificationCondition.VcSamModelForModification.transformSamToVcSamForModification
do! SafetySharp.Analysis.VerificationCondition.VcSamModelForModification.transformVcSamForModificationToVcSam
do! SafetySharp.Analysis.Modelchecking.Boogie.VcSamToBoogie.transformVcSamToBoogieWf
do! SafetySharp.Analysis.Modelchecking.Boogie.BoogieToString.boogieToStringWf
do! SafetySharp.Workflow.saveToFile *freshFileName*
do! SafetySharp.Analysis.Modelchecking.Boogie.ExecuteBoogie.runBoogie
```


[comment]: # (Encoded in UMLGraph from http://plantuml.sourceforge.net/activity.html)
[comment]: # (Need to include ; in each new line:)
[comment]: # (Need to Replace '(' by %28 and  ')' by %29 )
[comment]: # (Encoder available at http://www.gravizo.com/#converter )
