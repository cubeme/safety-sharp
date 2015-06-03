
// Visual Studio: execute selected code with ALT+ENTER. if dll must be reloaded, use "exit 0"

let path = __SOURCE_DIRECTORY__
// Alternative:
//   #if INTERACTIVE
//   System.IO.Directory.SetCurrentDirectory("<project_path>")
//   #endif

#r @"bin\Debug\SafetySharp.Documentation.Scripts.dll"
let useOnlyStochastic = false
let output = SafetySharp.Documentation.Scripts.TsamToReport.generateTexFile useOnlyStochastic (path+"/smokeTest8.tex") (path + "/../../../../Examples/SAM/smokeTest8.sam")

do printfn "%s" output