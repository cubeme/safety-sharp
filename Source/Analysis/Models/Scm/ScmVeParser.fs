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

module internal ScmVeParser =
    open FParsec
    open SafetySharp.Models.Scm
    open SafetySharp.Models.ScmHelpers
    open SafetySharp.GenericParsers
    
    [<RequireQualifiedAccess>]
    type IdentifierType =
        | Field
        | Var
        | Fault
        | Comp
        | NotDeclared
        

    type UserState = {
        CurrentLocation : string list;
        LocationToType : Map<string list,IdentifierType> ;
    }
        with
            member us.IsFullLocationOfType (location:string list) (id_type:IdentifierType) =
                if not(us.LocationToType.ContainsKey location) then
                    false
                else if (us.LocationToType.ContainsKey location) && (us.LocationToType.Item location = id_type) then
                    true
                else
                    false
            member us.IsIdentifierInCurrentLocationOfType (identifier:string) (id_type:IdentifierType) =
                let locationToCheck = identifier::us.CurrentLocation
                us.IsFullLocationOfType locationToCheck
            member us.pushCurrentLocation (compName:string) : UserState =
                { us with
                    UserState.CurrentLocation = compName::us.CurrentLocation;
                }                
            member us.popCurrentLocation : UserState =
                { us with
                    UserState.CurrentLocation = us.CurrentLocation.Tail;
                }
            member us.resetCurrentLocation : UserState =
                { us with
                    UserState.CurrentLocation = [];
                }
            static member initialUserState (scmModel:Scm.ScmModel) =
                let rec collectLocationsOfIdentifiers (parentLocation:string list) (currentCompDecl:CompDecl) : (string list*IdentifierType) list =
                    let currentLocation = (currentCompDecl.Comp.getName)::parentLocation
                    let identifiersFromSubs = currentCompDecl.Subs |> List.collect (collectLocationsOfIdentifiers currentLocation)
                    let identifiersFromHere =
                        let identifierFromFields = currentCompDecl.Fields |> List.map (fun field -> (field.getName::currentLocation,IdentifierType.Field)  )
                        let identifierFromFaults = currentCompDecl.Faults |> List.map (fun fault -> (fault.getName::currentLocation,IdentifierType.Fault) )
                        let identifierFromComp = (currentLocation,IdentifierType.Comp)
                        (identifierFromComp::identifierFromFields@identifierFromFaults)
                    (identifiersFromHere@identifiersFromSubs)
                let rootComponent = scmModel.getRootComp
                let locatedIdentifiers = collectLocationsOfIdentifiers []  (rootComponent)
                {
                    UserState.CurrentLocation = [];
                    UserState.LocationToType =  locatedIdentifiers |> Map.ofList;
                }

