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

namespace Modeling.``Binding Tests``

open System
open System.Linq
open System.Linq.Expressions
open System.Reflection
open NUnit.Framework
open SafetySharp.Modeling
open Modeling

[<AutoOpen>]
module private Helpers =
    let component' = OneFieldComponent ()
    do component'.FinalizeMetadata ()

    let reqPorts = component'.RequiredPorts :?> RequiredPortCollection
    let provPorts = component'.ProvidedPorts :?> ProvidedPortCollection

    let getPort name =
        component'.GetType().GetMethod (name, BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic)

    let getPorts name =
        component'.GetType().GetMethods(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic) |> Seq.filter (fun m -> m.Name = name)

[<TestFixture; Ignore>]
module ``Port class`` =
    [<Test>]
    let ``signatures of 'void -> void' ports shoud be compatible`` () =
        let port1 = Port (component', getPort "ReqPort1")
        let port2 = Port (component', getPort "ProvPort1")
        
        port1.IsCompatibleTo port2 =? true
        port1.IsCompatibleTo port1 =? true
        port2.IsCompatibleTo port1 =? true
        port2.IsCompatibleTo port2 =? true

    [<Test>]
    let ``signatures of 'int -> bool' ports shoud be compatible`` () =
        let port1 = Port (component', getPort "ReqPort2")
        let port2 = Port (component', getPort "ProvPort2")
        
        port1.IsCompatibleTo port2 =? true
        port1.IsCompatibleTo port1 =? true
        port2.IsCompatibleTo port1 =? true
        port2.IsCompatibleTo port2 =? true

    [<Test>]
    let ``signatures of 'int -> bool' and 'void -> void' ports shoud be incompatible`` () =
        let port1 = Port (component', getPort "ReqPort1")
        let port2 = Port (component', getPort "ProvPort1")
        let port3 = Port (component', getPort "ReqPort2")
        let port4 = Port (component', getPort "ProvPort2")
        
        port1.IsCompatibleTo port3 =? false
        port3.IsCompatibleTo port1 =? false
        port2.IsCompatibleTo port4 =? false
        port4.IsCompatibleTo port2 =? false

    [<Test>]
    let ``signatures of 'int -> bool' and 'int -> int' ports shoud be incompatible`` () =
        let port1 = Port (component', getPort "ReqPort1")
        let port2 = Port (component', getPort "ProvPort1")
        let port3 = Port (component', getPorts "OverloadedReqPort" |> Seq.head)
        let port4 = Port (component', getPorts "OverloadedProvPort" |> Seq.head)
        
        port1.IsCompatibleTo port3 =? false
        port3.IsCompatibleTo port1 =? false
        port2.IsCompatibleTo port4 =? false
        port4.IsCompatibleTo port2 =? false

[<TestFixture; Ignore>]
module ``PortSet class`` =
    [<Test>]
    let ``OfType method should return port of matching type (singleton set)`` () =
       let set = PortSet ("ReqPort1", component', getPorts "ReqPort1")
       set.Ports.Length =? 1
       set.OfType<Action>().Method =? getPort "ReqPort1"

       let set = PortSet ("ProvPort2", component', getPorts "ProvPort2")
       set.Ports.Length =? 1
       set.OfType<Func<int, bool>>().Method =? getPort "ProvPort2"

    [<Test>]
    let ``OfType method should throw for non-matching type (singleton set)`` () =
       let set = PortSet ("ReqPort1", component', getPorts "ReqPort1")
       set.Ports.Length =? 1
       raisesInvalidOpException (fun () -> set.OfType<Func<int, bool>>().Method =? getPort "ReqPort1")

       let set = PortSet ("ProvPort2", component', getPorts "ProvPort2")
       set.Ports.Length =? 1
       raisesInvalidOpException (fun () -> set.OfType<Func<int, int>>().Method =? getPort "ProvPort2")

    [<Test>]
    let ``OfType method should return port of matching type (non-singleton set)`` () =
       let set = PortSet ("OverloadedReqPort", component', getPorts "OverloadedReqPort")
       set.Ports.Length =? 2
       set.OfType<Func<int, int>>().Method =? (getPorts "OverloadedReqPort" |> Seq.head)
       set.OfType<Func<bool, bool>>().Method =? (getPorts "OverloadedReqPort" |> Seq.skip 1 |> Seq.head)

       let set = PortSet ("OverloadedProvPort", component', getPorts "OverloadedProvPort")
       set.Ports.Length =? 2
       set.OfType<Func<int, int>>().Method =? (getPorts "OverloadedProvPort" |> Seq.head)
       set.OfType<Func<bool, bool>>().Method =? (getPorts "OverloadedProvPort" |> Seq.skip 1 |> Seq.head)

    [<Test>]
    let ``OfType method should throw for non-matching type (non-singleton set)`` () =
       let set = PortSet ("OverloadedReqPort", component', getPorts "OverloadedReqPort")
       raisesInvalidOpException (fun () -> set.OfType<Action>().Method =? getPort "ReqPort1")

       let set = PortSet ("OverloadedProvPort", component', getPorts "OverloadedProvPort")
       raisesInvalidOpException (fun () -> set.OfType<Action>().Method =? getPort "ProvPort2")

[<TestFixture; Ignore>]
module ``ProvidedPortCollection class`` =
    [<Test>]
    let ``GetPortSets method`` () =
        provPorts.GetPortSets() |> List.map (fun p -> p.Name) |> List.sort =? ["OverloadedProvPort"; "OverloadedProvPort2"; "ProvPort1"; "ProvPort2"]

[<TestFixture; Ignore>]
module ``RequiredPortCollection class`` =
    [<Test>]
    let ``GetPortSets method`` () =
        reqPorts.GetPortSets() |> List.map (fun p -> p.Name) |> List.sort =? ["OverloadedReqPort"; "OverloadedReqPort2"; "ReqPort1"; "ReqPort2"]

    [<Test>]
    let ``Bind method: throws for failed bindings`` () =
        let port1 = Port (component', getPort "ReqPort1")
        let port2 = Port (component', getPort "ProvPort2")

        reqPorts.ClearBindings ()
        raises<BindingFailureException> (fun () -> reqPorts.Bind [port1] [port2] |> ignore)

    [<Test>]
    let ``Bind method: unambiguous binds of singleton sets`` () =
        let port1 = Port (component', getPort "ReqPort1")
        let port2 = Port (component', getPort "ProvPort1")

        reqPorts.ClearBindings ()
        reqPorts.Bind [port1] [port2] =? true
        reqPorts.Bindings =? [port1, port2]

        let port1 = Port (component', getPort "ReqPort2")
        let port2 = Port (component', getPort "ProvPort2")

        reqPorts.ClearBindings ()
        reqPorts.Bind [port1] [port2] =? true
        reqPorts.Bindings =? [port1, port2]

    [<Test>]
    let ``Bind method: unambiguous singleton binds of non-singleton sets`` () =
        let set1 = PortSet ("OverloadedReqPort", component', getPorts "OverloadedReqPort")
        let set2 = PortSet ("OverloadedProvPort", component', getPorts "OverloadedProvPort")

        reqPorts.ClearBindings ()
        reqPorts.Bind [set1.Ports.[0]] set2.Ports =? true
        reqPorts.Bindings =? [set1.Ports.[0], set2.Ports.[0]]

        reqPorts.ClearBindings ()
        reqPorts.Bind [set1.Ports.[1]] set2.Ports =? true
        reqPorts.Bindings =? [set1.Ports.[1], set2.Ports.[1]]

        reqPorts.ClearBindings ()
        reqPorts.Bind set1.Ports [set2.Ports.[0]] =? true
        reqPorts.Bindings =? [set1.Ports.[0], set2.Ports.[0]]

        reqPorts.ClearBindings ()
        reqPorts.Bind set1.Ports [set2.Ports.[1]] =? true
        reqPorts.Bindings =? [set1.Ports.[1], set2.Ports.[1]]

    [<Test>]
    let ``Bind method: unambiguous non-singleton binds of non-singleton sets`` () =
        let set1 = PortSet ("OverloadedReqPort2", component', getPorts "OverloadedReqPort2")
        let set2 = PortSet ("OverloadedProvPort2", component', getPorts "OverloadedProvPort2")

        reqPorts.ClearBindings ()
        reqPorts.Bind set1.Ports set2.Ports =? true
        reqPorts.Bindings =? [set1.Ports.[0], set2.Ports.[0]]

    [<Test>]
    let ``Bind method: throws for ambiguous binds`` () =
        let set1 = PortSet ("OverloadedReqPort", component', getPorts "OverloadedReqPort")
        let set2 = PortSet ("OverloadedProvPort", component', getPorts "OverloadedProvPort")

        reqPorts.ClearBindings ()
        raises<AmbiguousBindingException> (fun () -> reqPorts.Bind set1.Ports set2.Ports |> ignore)