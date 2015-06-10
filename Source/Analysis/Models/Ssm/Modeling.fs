// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Models

open Mono.Cecil
open SafetySharp
open SafetySharp.Modeling
open SafetySharp.Reflection

[<AutoOpen>]
module Extensions =
    
    type Component with
        /// Gets the initial values of given field.
        member internal this.GetInitialValuesOfField (field : FieldDefinition) =
            nullArg field "field"

            // We have to find a FieldInfo instance that resolves to the given FieldDefinition
            match this.Fields.Keys |> Seq.tryFind (fun info -> (field.Module.Import(info).Resolve ()) = field) with
            | Some f -> this.Fields.[f] |> Array.toList
            | None   -> 
                invalidArg true "field" "Unable to retrieve initial values for field '%s'." field.FullName
                [] // Required, but cannot be reached

    type Model with
        /// Gets the metadata provider for the model.
        member internal this.GetMetadataProvider () =
            let metadataTypes = seq {
                yield typeof<RootComponent>
                yield! this.Components |> Seq.map (fun c -> c.GetType ())
                yield! this.Components |> Seq.collect (fun c -> c.Faults |> Seq.map (fun f -> f.GetType ()))
            }
            
            MetadataProvider (metadataTypes |> Seq.toList)