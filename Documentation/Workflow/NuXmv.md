# The NuXmv pipeline to verify SafetySharp models

## Requirements (Windows)

* NuXmv V 1.0.0 https://nuxmv.fbk.eu/

## Workflow from SCM to NuXmv



```
do! ScmWorkflow.setPlainModelState scm
do! SafetySharp.Models.ScmRewriterFlattenModel.flattenModel
do! SafetySharp.Models.ScmToSam.transformIscmToSam
do! SafetySharp.Analysis.VerificationCondition.VcSamModelForModification.transformSamToVcSamForModification
do! SafetySharp.Analysis.Modelchecking.NuXmv.SamToNuXmvWp.transformConfiguration_fromVcSam
//do! missing
//do! SafetySharp.Workflow.saveToFile *freshFileName*
```


[comment]: # (Encoded in UMLGraph from http://plantuml.sourceforge.net/activity.html)
[comment]: # (Need to include ; in each new line:)
[comment]: # (Need to Replace '(' by %28 and  ')' by %29 )
[comment]: # (Encoder available at http://www.gravizo.com/#converter )
