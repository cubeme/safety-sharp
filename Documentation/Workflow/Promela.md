# The promela pipeline to verify SafetySharp models

## Requirements (Windows)

* spin627.exe in Dependency folder
* C-Compiler from MinGW http://www.mingw.org/

## Workflow from SCM to Promela



```
do! ScmWorkflow.setPlainModelState scm
do! SafetySharp.Models.ScmRewriterFlattenModel.flattenModel
do! SafetySharp.Models.ScmToSam.transformIscmToSam
do! SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf
do! SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString.workflow
do! SafetySharp.Workflow.saveToFile *freshFileName*
do! SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPan
```


[comment]: # (Encoded in UMLGraph from http://plantuml.sourceforge.net/activity.html)
[comment]: # (Need to include ; in each new line:)
[comment]: # (Need to Replace '(' by %28 and  ')' by %29 )
[comment]: # (Encoder available at http://www.gravizo.com/#converter )

![Alt text](http://g.gravizo.com/g?
@startuml;
%28*%29 --> "SCM-Model";
-->[ScmWorkflow.setPlainModelState] "SCM model %28with IScm-Interface%29";
-->[SafetySharp.Models.ScmRewriterFlattenModel.flattenModel] "Flattened SCM model %28with IScm interface%29";
-->[SafetySharp.Models.ScmToSam.transformIscmToSam] "SAM model";
-->[SafetySharp.Analysis.Modelchecking.PromelaSpin.SamToPromela.transformConfigurationWf] "Promela code as AST";
-->[SafetySharp.Analysis.Modelchecking.PromelaSpin.PromelaToString] "Promela code as string";
-->[SafetySharp.Workflow.saveToFile] "Saved Promela Code";
-->[SafetySharp.Analysis.Modelchecking.PromelaSpin.ExecuteSpin.runPan] "result string of pan";
--> %28*%29;
@enduml
)