open System
open System.Globalization
open System.IO
open System.Text
open System.Threading

//====================================================================================================================
// F# type definitions
//====================================================================================================================

type Property = { 
    Name : string
    Type : string
    Comment : string 
}

type Class = { 
    Name : string
    Base : string
    Abstract : bool
    Properties : Property list 
}

type Namespace = { 
    Name : string
    Classes : Class list 
}

//====================================================================================================================
// Metamodel element definitions
//====================================================================================================================

let elements = [
    {
        Namespace.Name = "SafetySharp.Metamodel.Declarations"
        Namespace.Classes = 
        [
            {
                Name = "TypeDeclaration"
                Base = "MetamodelElement"
                Abstract = true
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "string"
                        Comment = "The name of the declared type."
                    }
                    {
                        Name = "Namespace"
                        Type = "string"
                        Comment = "The namespace the type is declared in."
                    }
                ]
            }
            {   
                Name = "ClassDeclaration"
                Base = "TypeDeclaration"
                Abstract = false
                Properties = 
                [
                    {
                        Name = "Members"
                        Type = "bool"
                        Comment = "..."
                    }
                ]
            }
            {   
                Name = "ComponentDeclaration"
                Base = "TypeDeclaration"
                Abstract = false
                Properties = []
            }
            {   
                Name = "MemberDeclaration"
                Base = "MetamodelElement"
                Abstract = true
                Properties = []
            }
            {   
                Name = "FieldDeclaration"
                Base = "MemberDeclaration"
                Abstract = false
                Properties = []
            }
            {   
                Name = "PropertyDeclaration"
                Base = "MemberDeclaration"
                Abstract = false
                Properties = []
            }
            {   
                Name = "StateVariableDeclaration"
                Base = "MemberDeclaration"
                Abstract = false
                Properties = []
            }
        ]
    }
    {
        Namespace.Name = "SafetySharp.Metamodel.Expressions"
        Namespace.Classes = 
        [
            {   
                Name = "Expression"
                Base = "MetamodelElement"
                Abstract = true
                Properties = []
            }
            {   
                Name = "GuardedCommandExpression"
                Base = "Expression"
                Abstract = false
                Properties = []
            }
        ]
    }
    {
        Namespace.Name = "SafetySharp.Metamodel.Statements"
        Namespace.Classes = 
        [
            {   
                Name = "Statement"
                Base = "MetamodelElement"
                Abstract = true
                Properties = []
            }
            {   
                Name = "ExpressionStatement"
                Base = "Statement"
                Abstract = false
                Properties = []
            }
            {   
                Name = "BlockStatement"
                Base = "Statement"
                Abstract = false
                Properties = []
            }
        ]
    }
]

//====================================================================================================================
// CodeWriter helper class
//====================================================================================================================

type CodeWriter() as this =
    let output = new StringBuilder()
    let mutable atBeginningOfLine = true
    let mutable indent = 0
    do this.AppendHeader()

    member public this.Append (s : string) =
        this.AddIndentation()
        output.Append s |> ignore

    member public this.AppendLine s =
        this.Append s
        this.Newline()

    member public this.Newline() =
        output.AppendLine() |> ignore
        atBeginningOfLine <- true

    member public this.AppendBlockStatement content =
        this.EnsureNewline()
        this.AppendLine("{")
        this.IncreaseIndent()

        content()

        this.EnsureNewline()
        this.DecreaseIndent()
        this.Append("}")

        this.Newline()

    member public this.WriteToFile path =
        File.WriteAllText(path, output.ToString())
        printfn "'%s' has been generated." path

    member private this.EnsureNewline() =
        if not atBeginningOfLine then
            this.Newline()

    member private this.AddIndentation() =
        if atBeginningOfLine then 
            atBeginningOfLine <- false
            for i = 1 to indent do
                output.Append("    ") |> ignore

    member public this.IncreaseIndent() = indent <- indent + 1
    member public this.DecreaseIndent() = indent <- indent - 1

    member private this.AppendHeader() =
        this.AppendLine("//------------------------------------------------------------------------------")
        this.AppendLine("// <auto-generated>")
        this.AppendLine(sprintf "//     Generated by the '%s' script." __SOURCE_FILE__)
        this.AppendLine(sprintf "//     %s, %s" (DateTime.Now.ToLongDateString()) (DateTime.Now.ToLongTimeString()))
        this.AppendLine("//")
        this.AppendLine("//     Changes to this file may cause incorrect behavior and will be lost if")
        this.AppendLine("//     the code is regenerated.")
        this.AppendLine("// </auto-generated>")
        this.AppendLine("//------------------------------------------------------------------------------")
        this.Newline()

//====================================================================================================================
// Code generation
//====================================================================================================================

// Set the thread culture to the invariant culture so that we don't get localized ToString() output for floating
// point values
Thread.CurrentThread.CurrentCulture <- CultureInfo.InvariantCulture;
Thread.CurrentThread.CurrentUICulture <- CultureInfo.InvariantCulture;

// Generate the code
let generateCode =
    let output = new CodeWriter()

    let startWithLowerCase (s : string) =
        sprintf "%c%s" <| Char.ToLower(s.[0]) <| s.Substring(1)

    let getParameterName (s : string) = 
        let s = startWithLowerCase s
        match s with
        | "bool"
        | "byte"
        | "sbyte"
        | "short"
        | "ushort"
        | "int"
        | "uint"
        | "long"
        | "ulong"
        | "double"
        | "float"
        | "decimal"
        | "string"
        | "char"
        | "object"
        | "typeof"
        | "sizeof"
        | "null"
        | "true"
        | "false"
        | "if"
        | "else"
        | "while"
        | "for"
        | "foreach"
        | "do"
        | "switch"
        | "case"
        | "default"
        | "lock"
        | "try"
        | "throw"
        | "catch"
        | "finally"
        | "goto"
        | "break"
        | "continue"
        | "return"
        | "public"
        | "private"
        | "internal"
        | "protected"
        | "static"
        | "readonly"
        | "sealed"
        | "const"
        | "new"
        | "override"
        | "abstract"
        | "virtual"
        | "partial"
        | "ref"
        | "out"
        | "in"
        | "where"
        | "params"
        | "this"
        | "base"
        | "namespace"
        | "using"
        | "class"
        | "struct"
        | "interface"
        | "delegate"
        | "checked"
        | "get"
        | "set"
        | "add"
        | "remove"
        | "operator"
        | "implicit"
        | "explicit"
        | "fixed"
        | "extern"
        | "event"
        | "enum"
        | "unsafe"
            -> sprintf "@%s" s 
        | _
            -> s

    let classes = elements |> List.collect (fun n -> n.Classes)
    let rec getBaseProperties (c : Class) = 
        if c.Base = "MetamodelElement" then 
            []
        else
            let baseClass = classes |> List.filter (fun c' -> c'.Name = c.Base)
            if baseClass |> List.length <> 1 then
                failwith "Class '%s' has unknown base '%s'." c.Name c.Base
            let baseClass = baseClass |> List.head
            getBaseProperties baseClass @ baseClass.Properties

    let allProperties (c : Class) = 
        getBaseProperties c @ c.Properties

    let collect separator proj (p : Property list) = 
        let collected = p |> List.map proj
        String.Join(separator, collected)

    let generateProperty (p : Property) =
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Gets %s" <| startWithLowerCase p.Comment)
        output.AppendLine("/// </summary>")
        output.AppendLine(sprintf "public %s %s { get; private set; }" p.Type p.Name)
        
    let generateConstructor (c : Class) = 
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Initializes a new instance of the <see cref=\"%s\" /> class." <| c.Name)
        output.AppendLine("/// </summary>")
        for p in allProperties c do
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)

        let parameters = allProperties c |> collect ", " (fun p -> sprintf "%s %s" p.Type <| getParameterName p.Name)
        let visibility = if c.Abstract then "protected" else "public"
        output.AppendLine(sprintf "%s %s(%s)" visibility c.Name parameters)

        output.IncreaseIndent()
        let baseParams = getBaseProperties c |> collect ", " (fun p -> getParameterName p.Name)
        output.AppendLine(sprintf ": base(%s)" baseParams)
        output.DecreaseIndent()

        output.AppendBlockStatement <| fun () ->
            for p in c.Properties do
                output.AppendLine(sprintf "%s = %s;" p.Name <| getParameterName p.Name)

            if allProperties c |> List.length > 0 then
                output.AppendLine("Validate();")

    let generateValidateMethod (c : Class) =
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Validates the properties of a <see cref=\"%s\" /> instance." c.Name)
        output.AppendLine("/// </summary>")
        output.AppendLine("partial void Validate();")

    let generateWithMethods (c: Class) =
        for p in allProperties c do
            output.AppendLine("/// <summary>")
            output.AppendLine(sprintf "///     Replaces the %s in a copy of the <see cref=\"%s\" /> instance." <| startWithLowerCase p.Name <| c.Name)
            output.AppendLine("/// </summary>")
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)
            output.AppendLine(sprintf "public %s With%s(%s %s)" c.Name p.Name p.Type <| getParameterName p.Name)
            output.AppendBlockStatement <| fun () ->
                let parameters = allProperties c |> collect ", " (fun p' -> 
                    if p' = p then getParameterName p'.Name
                    else p'.Name
                )
                output.AppendLine(sprintf "return Update(%s);" parameters)
            output.Newline()

    let generateUpdateMethod (c : Class) =
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Returns a new <see cref=\"%s\" /> instance if any properties require an update." c.Name)
        output.AppendLine("/// </summary>")

        for p in allProperties c do
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)

        let parameters = allProperties c |> collect ", " (fun p' -> sprintf "%s %s" p'.Type <| getParameterName p'.Name)
        output.AppendLine(sprintf "public %s Update(%s)" c.Name parameters)
        output.AppendBlockStatement <| fun () ->
            let checkModification = allProperties c |> collect " || " (fun p' -> sprintf "%s != %s" p'.Name <| getParameterName p'.Name)
            output.AppendLine(sprintf "if (%s)" checkModification)

            output.IncreaseIndent()
            let parameters = allProperties c |> collect ", " (fun p' -> getParameterName p'.Name)
            output.AppendLine(sprintf "return new %s(%s);" c.Name parameters)
            output.DecreaseIndent()

            output.Newline()
            output.AppendLine("return this;")

    let generateClass (c : Class) =
        let abstractKeyword = if c.Abstract then " abstract " else " "
        output.AppendLine(sprintf "public%spartial class %s : %s" abstractKeyword c.Name c.Base)
        output.AppendBlockStatement <| fun () ->
            for p in c.Properties do
                generateProperty p
                output.Newline()

            generateConstructor c

            let hasProperties = allProperties c |> List.length > 0
            if hasProperties then
                output.Newline()
                generateValidateMethod c

            if not c.Abstract && hasProperties then
                output.Newline()
                generateWithMethods c
                generateUpdateMethod c

    let generateNamespace (n : Namespace) =
        output.AppendLine(sprintf "namespace %s" n.Name)
        output.AppendBlockStatement <| fun () ->
            output.AppendLine("using System;")
            output.Newline()

            let count = n.Classes |> List.length
            let mutable i = 0
            for c in n.Classes do
               generateClass c
               i <- i + 1
               if i <> count then output.Newline()

    let count = elements |> List.length
    let mutable i = 0
    for n in elements do
        generateNamespace n
        i <- i + 1
        if i <> count then output.Newline()

    // Write the enumeration file
    output.WriteToFile "SafetySharp/Metamodel/Elements.Generated.cs"

generateCode
printfn "Done generating code."