// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

open System
open System.Globalization
open System.IO
open System.Text
open System.Threading

//====================================================================================================================
// Metamodel code generator
//====================================================================================================================

// This F# script generates C# code for metamodel elements and visitors. The generated code is written to the output
// file. Metamodel elements are immutable, however, C# doesn't support a concise syntax for the specification of 
// immutable data types. From the metadata provided below, partial classes are generated for the metamodel elements
// and visitors containing all the boilerplate code:
// - Get-only properties
// - Constructors taking values for all properties, optionally performing validation
// - Additional validation is supported through a partial Validate() method
// - A With...(...) method for each property that creates a copy of the object, changing only the value of the given
//   property; if the property value has not changed, no copy is made and the original object is returned
// - An Add...(...) method for each property of collection type that creates a copy of the object, adding the given
//   values to the collection property; if the collection has not changed, no copy is made and the original object 
//   is returned
// - An Update(...) method that creates a new instance of the object if any of the property values have changed; if
//   none have changed, no copy is made and the original object is returned
// - Constructors, With* methods and Update() all take inherited properties into account, generating the appropriate
//   code and methods instead of relying on chains of virtual function calls
// - Accept() methods for metamodel visitors

/// <summary>
/// The path to the file the generated C# code should be written to.
/// </summary>
let outputFile = "SafetySharp/Metamodel/Metamodel.Generated.cs"

//====================================================================================================================
// F# type definitions
//====================================================================================================================

type CollectionType = 
    | Singleton
    | Array
    | List

type Validation =
    | None
    | NotNull
    | NotNullOrWhitespace

type Property = { 
    Name : string
    Type : string
    CollectionType : CollectionType
    Validation : Validation
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
        Name = "SafetySharp.Metamodel"
        Classes =
        [
            {
                Name = "Identifier"
                Base = "MetamodelElement"
                Abstract = false
                Properties =
                [
                    { 
                        Name = "Name"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The name of the identifier."
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Declarations"
        Classes = 
        [
            {
                Name = "TypeDeclaration"
                Base = "MetamodelElement"
                Abstract = true
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The name of the declared type."
                    }
                    {
                        Name = "Namespace"
                        Type = "string"
                        CollectionType = Singleton
                        Validation = NotNullOrWhitespace
                        Comment = "The namespace the type is declared in."
                    }
                    {
                        Name = "Members"
                        Type = "MemberDeclaration"
                        CollectionType = Array
                        Validation = None
                        Comment = "The declared members of the type."
                    }
                ]
            }
            {   
                Name = "ClassDeclaration"
                Base = "TypeDeclaration"
                Abstract = false
                Properties = []
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
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The name of the property."
                    }
                    {
                        Name = "Type"
                        Type = "TypeReference"
                        CollectionType = Singleton
                        Validation = NotNull
                        Comment = "The type of the property."
                    }
                    {
                        Name = "Getter"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The body of the property's getter."
                    }
                    {
                        Name = "Setter"
                        Type = "Statement"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The body of the property's setter."
                    }
                ]
            }
            {   
                Name = "StateVariableDeclaration"
                Base = "MemberDeclaration"
                Abstract = false
                Properties = 
                [
                    {
                        Name = "Name"
                        Type = "Identifier"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The name of the state variable."
                    }
                    {
                        Name = "Type"
                        Type = "TypeReference"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The type of the state variable."
                    }
                ]
            }
        ]
    }
    {
        Name = "SafetySharp.Metamodel.Expressions"
        Classes = 
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
        Name = "SafetySharp.Metamodel.Statements"
        Classes = 
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
    {
        Name = "SafetySharp.Metamodel.TypeReferences"
        Classes = 
        [
            {   
                Name = "TypeReference"
                Base = "MetamodelElement"
                Abstract = true
                Properties = []
            }
            {   
                Name = "VoidTypeReference"
                Base = "TypeReference"
                Abstract = false
                Properties = []
            }
            {   
                Name = "BooleanTypeReference"
                Base = "TypeReference"
                Abstract = false
                Properties = []
            }
            {   
                Name = "IntegerTypeReference"
                Base = "TypeReference"
                Abstract = false
                Properties = []
            }
            {   
                Name = "InterfaceTypeReference"
                Base = "TypeReference"
                Abstract = false
                Properties = 
                [
                    {
                        Name = "Slot"
                        Type = "int"
                        CollectionType = Singleton
                        Validation = None
                        Comment = "The slot of the interface declaration in the model's type information table."
                    }
                ]
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

// Set the thread culture to the invariant culture so that we don't get localized ToString() output
Thread.CurrentThread.CurrentCulture <- CultureInfo.InvariantCulture;
Thread.CurrentThread.CurrentUICulture <- CultureInfo.InvariantCulture;

// Generate the code
let generateCode () =
    let output = new CodeWriter()

    let startWithLowerCase (s : string) =
        sprintf "%c%s" <| Char.ToLower(s.[0]) <| s.Substring(1)

    let getParameterName (s : string) = 
        let s = startWithLowerCase s
        match s with
        | "bool" | "byte" | "sbyte" | "short" | "ushort" | "int" | "uint" | "long" | "ulong" | "double" | "float" | "decimal" 
        | "string" | "char" | "object" | "typeof" | "sizeof" | "null" | "true" | "false" | "if" | "else"  | "while" | "for"
        | "foreach" | "do" | "switch" | "case" | "default" | "lock" | "try" | "throw" | "catch" | "finally" | "goto" | "break"
        | "continue" | "return" | "public" | "private" | "internal" | "protected" | "static" | "readonly" | "sealed" | "const"
        | "new" | "override" | "abstract" | "virtual" | "partial" | "ref" | "out" | "in" | "where" | "params" | "this" | "base"
        | "namespace" | "using" | "class" | "struct" | "interface" | "delegate" | "checked" | "get" | "set" | "add" | "remove"
        | "operator" | "implicit" | "explicit" | "fixed" | "extern" | "event" | "enum" | "unsafe"
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
                failwithf "Class '%s' has unknown base '%s'." c.Name c.Base
            let baseClass = baseClass |> List.head
            getBaseProperties baseClass @ baseClass.Properties

    let allProperties (c : Class) = 
        getBaseProperties c @ c.Properties

    let collect separator proj (p : Property list) = 
        let collected = p |> List.map proj
        String.Join(separator, collected)

    let visitorTypeParam typeParam = if typeParam = "" then "" else sprintf "<%s>" typeParam
    let visitorReturnType typeParam = if typeParam = "" then "void" else typeParam

    let writeNamespaces () =
        output.AppendLine("using System;")
        output.AppendLine("using System.Collections.Immutable;");
        output.Newline()

        output.AppendLine("using SafetySharp.Utilities;");
        for n in elements do
            output.AppendLine(sprintf "using %s;" n.Name)

        output.Newline()

    let getType (p : Property) =
        match p.CollectionType with
        | Singleton -> p.Type
        | Array -> sprintf "ImmutableArray<%s>" p.Type
        | List -> sprintf "ImmutableList<%s>" p.Type

    let generateProperty (p : Property) =
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Gets %s" <| startWithLowerCase p.Comment)
        output.AppendLine("/// </summary>")
        output.AppendLine(sprintf "public %s %s { get; private set; }" <| getType p <| p.Name)

    let generateValidation (p : Property) =
        let parameterName = getParameterName p.Name
        match p.Validation with
        | None ->
            ()
        | NotNull -> 
            output.AppendLine(sprintf "Assert.ArgumentNotNull(%s, () => %s);" parameterName parameterName)
        | NotNullOrWhitespace -> 
            output.AppendLine(sprintf "Assert.ArgumentNotNullOrWhitespace(%s, () => %s);" parameterName parameterName)
        
    let generateConstructor (c : Class) = 
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Initializes a new instance of the <see cref=\"%s\" /> class." <| c.Name)
        output.AppendLine("/// </summary>")
        for p in allProperties c do
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)

        let parameters = allProperties c |> collect ", " (fun p -> sprintf "%s %s" <| getType p <| getParameterName p.Name)
        let visibility = if c.Abstract then "protected" else "public"
        output.AppendLine(sprintf "%s %s(%s)" visibility c.Name parameters)

        output.IncreaseIndent()
        let baseParams = getBaseProperties c |> collect ", " (fun p -> getParameterName p.Name)
        output.AppendLine(sprintf ": base(%s)" baseParams)
        output.DecreaseIndent()

        output.AppendBlockStatement <| fun () ->
            let validatedProperties = c.Properties |> List.filter (fun p -> p.Validation <> None)
            if validatedProperties |> List.length > 0 then
                for p in validatedProperties do
                    generateValidation p
                output.Newline()

            if c.Properties |> List.length > 0 then
                let parameters = c.Properties |> collect ", " (fun p -> getParameterName p.Name)
                output.AppendLine(sprintf "Validate(%s);" parameters)

            for p in c.Properties do
                output.AppendLine(sprintf "%s = %s;" p.Name <| getParameterName p.Name)

    let generateValidateMethod (c : Class) =
        output.AppendLine("/// <summary>")
        output.AppendLine("///     Validates all of the given property values.")
        output.AppendLine("/// </summary>")

        for p in c.Properties do
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)

        let parameters = c.Properties |> collect ", " (fun p' -> sprintf "%s %s" <| getType p' <| getParameterName p'.Name)
        output.AppendLine(sprintf "partial void Validate(%s);" parameters)

    let generateWithMethods (c: Class) =
        for p in allProperties c do
            output.AppendLine("/// <summary>")
            output.AppendLine(sprintf "///     Creates a copy of the <see cref=\"%s\" /> instance, changing only the value of the" c.Name)
            output.AppendLine(sprintf "///     <see cref=\"%s.%s\" /> property; if the property value has not changed, " c.Name p.Name)
            output.AppendLine("///     no copy is made and the original object is returned.")
            output.AppendLine("/// </summary>")
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)
            output.AppendLine(sprintf "public %s With%s(%s %s)" c.Name p.Name <| getType p <| getParameterName p.Name)
            output.AppendBlockStatement <| fun () ->
                let parameters = allProperties c |> collect ", " (fun p' -> 
                    if p' = p then getParameterName p'.Name
                    else p'.Name
                )
                output.AppendLine(sprintf "return Update(%s);" parameters)
            output.Newline()

    let generateAddMethods (c : Class) =
        let collectionProperties = allProperties c |> List.filter (fun p -> p.CollectionType <> Singleton)
        for p in collectionProperties do
            output.AppendLine("/// <summary>")
            output.AppendLine(sprintf "///     Creates a copy of the <see cref=\"%s\" /> instance, adding the given values to the" c.Name)
            output.AppendLine(sprintf "///     <see cref=\"%s.%s\" /> collection; if <paramref name=\"%s\" /> is empty, " c.Name p.Name <| getParameterName p.Name)
            output.AppendLine("///     no copy is made and the original instance is returned.")
            output.AppendLine("/// </summary>")
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)
            output.AppendLine(sprintf "public %s Add%s(params %s[] %s)" c.Name p.Name p.Type <| getParameterName p.Name)
            output.AppendBlockStatement <| fun () ->
                output.AppendLine(sprintf "return With%s(%s.AddRange(%s));" p.Name p.Name <| getParameterName p.Name)
            output.Newline()

    let generateUpdateMethod (c : Class) =
        output.AppendLine("/// <summary>")
        output.AppendLine(sprintf "///     Creates a new instance of the <see cref=\"%s\" /> class if any of the property values" c.Name)
        output.AppendLine(sprintf "///     have changed; if none have changed, no copy is made and the original instance is returned.")
        output.AppendLine("/// </summary>")

        for p in allProperties c do
            output.AppendLine(sprintf "/// <param name=\"%s\">%s</param>" <| startWithLowerCase p.Name <| p.Comment)

        let parameters = allProperties c |> collect ", " (fun p' -> sprintf "%s %s" <| getType p' <| getParameterName p'.Name)
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

    let generateAcceptMethod (c : Class) typeParam =
        let curlyTypeParam = if typeParam = "" then "" else sprintf "{%s}" typeParam
        output.AppendLine("/// <summary>")
        output.AppendLine("///     Implements the visitor pattern, calling <paramref name=\"visitor\" />'s")
        output.AppendLine(sprintf "///     <see cref=\"MetamodelVisitor%s.Visit%s(%s)\" /> method." curlyTypeParam c.Name c.Name)
        output.AppendLine("/// </summary>")
        if typeParam <> "" then
            output.AppendLine("/// <typeparam name=\"TResult\">The type of the value returned by <paramref name=\"visitor\" />.</typeparam>")
        output.AppendLine("/// <param name=\"visitor\">The visitor the type-specific visit method should be invoked on.</param>")
        let bracketedTypeParam = visitorTypeParam typeParam
        let returnType = visitorReturnType typeParam
        output.AppendLine(sprintf "public override %s Accept%s(MetamodelVisitor%s visitor)" returnType bracketedTypeParam bracketedTypeParam)
        output.AppendBlockStatement <| fun () ->
            let returnKeyword = if typeParam = "" then "" else "return "
            output.AppendLine("Assert.ArgumentNotNull(visitor, () => visitor);")
            output.AppendLine(sprintf "%svisitor.Visit%s(this);" returnKeyword c.Name)

    let generateClass (c : Class) =
        let abstractKeyword = if c.Abstract then " abstract " else " "
        output.AppendLine(sprintf "public%spartial class %s : %s" abstractKeyword c.Name c.Base)
        output.AppendBlockStatement <| fun () ->
            for p in c.Properties do
                generateProperty p
                output.Newline()

            generateConstructor c

            if c.Properties |> List.length > 0 then
                output.Newline()
                generateValidateMethod c

            if not c.Abstract && allProperties c |> List.length > 0 then
                output.Newline()
                generateWithMethods c
                generateAddMethods c
                generateUpdateMethod c

            if not c.Abstract then
                output.Newline()
                generateAcceptMethod c ""
                output.Newline()
                generateAcceptMethod c "TResult"

    let generateNamespace (n : Namespace) =
        output.AppendLine(sprintf "namespace %s" n.Name)
        output.AppendBlockStatement <| fun () ->
            writeNamespaces ()

            let count = n.Classes |> List.length
            let mutable i = 0
            for c in n.Classes do
               generateClass c
               i <- i + 1
               if i <> count then output.Newline()

    let generateVisitors () =
        let nonAbstractClasses = classes |> List.filter (fun c -> not c.Abstract)
        let generateVisitor typeParam =
            let bracketedTypeParam = visitorTypeParam typeParam
            let returnType = visitorReturnType typeParam
            output.AppendLine(sprintf "public abstract partial class MetamodelVisitor%s" bracketedTypeParam)
            output.AppendBlockStatement <| fun () ->
                let count = nonAbstractClasses |> List.length
                let mutable i = 0
                for c in nonAbstractClasses do
                    let parameterName = getParameterName c.Name
                    output.AppendLine("/// <summary>")
                    output.AppendLine(sprintf "///     Visits a metamodel element of type <see cref=\"%s\" />." c.Name)
                    output.AppendLine("/// </summary>")
                    output.AppendLine(sprintf "/// <param name=\"%s\">The <see cref=\"%s\" /> instance that should be visited.</param>" <| startWithLowerCase c.Name <| c.Name)
                    output.AppendLine(sprintf "public virtual %s Visit%s(%s %s)" returnType c.Name c.Name parameterName)
                    output.AppendBlockStatement <| fun () ->
                        output.AppendLine(sprintf "Assert.ArgumentNotNull(%s, () => %s);" parameterName parameterName)
                        if typeParam <> "" then
                            output.AppendLine(sprintf "return default(%s);" typeParam)
                    i <- i + 1
                    if i <> count then
                        output.Newline()

        let generateRewriter () =
            let isRewriteable typeName = classes |> List.exists (fun c -> c.Name = typeName)
            output.AppendLine("public abstract partial class MetamodelRewriter : MetamodelVisitor<MetamodelElement>")
            output.AppendBlockStatement <| fun () ->
                let count = nonAbstractClasses |> List.length
                let mutable i = 0
                for c in nonAbstractClasses do
                    let parameterName = getParameterName c.Name
                    output.AppendLine("/// <summary>")
                    output.AppendLine(sprintf "///     Rewrites a metamodel element of type <see cref=\"%s\" />." c.Name)
                    output.AppendLine("/// </summary>")
                    output.AppendLine(sprintf "/// <param name=\"%s\">The <see cref=\"%s\" /> instance that should be rewritten.</param>" <| startWithLowerCase c.Name <| c.Name)
                    output.AppendLine(sprintf "public override MetamodelElement Visit%s(%s %s)" c.Name c.Name parameterName)
                    output.AppendBlockStatement <| fun () ->
                        output.AppendLine(sprintf "Assert.ArgumentNotNull(%s, () => %s);" parameterName parameterName)

                        let properties = allProperties c
                        if properties |> List.length = 0 then
                            output.AppendLine(sprintf "return %s;" parameterName)
                        else
                            output.Newline()
                            for p in properties do
                                if isRewriteable p.Type then
                                    let cast = if p.CollectionType <> Singleton then "" else sprintf "(%s)" p.Type
                                    output.AppendLine(sprintf "var %s = %sVisit(%s.%s);" <| getParameterName p.Name <| cast <| parameterName <| p.Name)
                                else
                                    output.AppendLine(sprintf "var %s = %s.%s;" <| getParameterName p.Name <| parameterName <| p.Name)

                            let parameters = allProperties c |> collect ", " (fun p' -> getParameterName p'.Name)
                            output.AppendLine(sprintf "return %s.Update(%s);" parameterName parameters)

                    i <- i + 1
                    if i <> count then
                        output.Newline()

        output.AppendLine("namespace SafetySharp.Metamodel")
        output.AppendBlockStatement <| fun () ->
            writeNamespaces ()

            output.Newline()
            generateVisitor ""

            output.Newline()
            generateVisitor "TResult"

            output.Newline()
            generateRewriter ()

    for n in elements do
        generateNamespace n
        output.Newline()
        
    generateVisitors ()    
    output.WriteToFile outputFile

let writeColored s c =
    let c' = Console.ForegroundColor
    Console.ForegroundColor <- c

    printfn "%s" s
    Console.ForegroundColor <- c'

try
    generateCode ()
    writeColored "Done generating code." ConsoleColor.DarkGreen
with
    | e ->
        writeColored e.Message ConsoleColor.DarkRed
