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

namespace SafetySharp.Models.Scm

module internal ScmHelpers =

    // path = leaf :: parent_of_leaf :: ... :: root
    let getCompDeclFromPath (model:CompDecl) (path: Comp list) : CompDecl =
        let rec getCompDeclFromRevPath (current_component:CompDecl) (rev_path: Comp list) : CompDecl =
            if rev_path.IsEmpty then
                current_component
            else
                let subComponent =
                    current_component.Subs |> List.find (fun elem -> elem.Comp = rev_path.Head)
                getCompDeclFromRevPath subComponent rev_path.Tail
        let reverseList = List.rev path
        assert (reverseList.Head = model.Comp)
        getCompDeclFromRevPath model reverseList.Tail

    let getCompDeclParentFromPath (model:CompDecl) (path: Comp list) : CompDecl =
        // minimal path size is 2
        let rec getCompDeclFromRevPath (current_component:CompDecl) (rev_path: Comp list) : CompDecl =
            if rev_path.IsEmpty then
                current_component
            else
                let subComponent =
                    current_component.Subs |> List.find (fun elem -> elem.Comp = rev_path.Head)
                getCompDeclFromRevPath subComponent rev_path.Tail
        let listWithoutChild = path.Tail
        let reverseList = List.rev listWithoutChild
        assert (reverseList.Head = model.Comp)
        getCompDeclFromRevPath model reverseList.Tail

    let rec replaceComp (model:CompDecl) (pathToReplace: Comp list) (newComponent:CompDecl) : CompDecl =
        if pathToReplace.Head = model.Comp && pathToReplace.Tail = [] then
            //root should be replaced
            newComponent
        else
            //parent: We get the parent, where we correct the old node with the new node
            let parentNode = getCompDeclParentFromPath model pathToReplace
            let nodeToReplace = pathToReplace.Head
            let replaceSubNode (element:CompDecl) =
                if element.Comp = pathToReplace.Head then
                    newComponent
                else
                    element
            let newSubs = parentNode.Subs |> List.map replaceSubNode
            let newParent =
                { parentNode with
                    CompDecl.Subs = newSubs;
                }
            // recursively replace parent
            replaceComp model pathToReplace.Tail newParent



