
// Visual Studio: execute selected code with ALT+ENTER

let path = __SOURCE_DIRECTORY__

#r @"bin\Debug\SafetySharp.Documentation.Scripts.dll"
let useOnlyStochastic = false
let output = SafetySharp.Documentation.Scripts.TsamToTex.generateTexFile useOnlyStochastic (path + "/../../../../Examples/SAM/smokeTest8.sam")

do printfn "%s" output