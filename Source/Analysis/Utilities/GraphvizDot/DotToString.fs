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

namespace SafetySharp.GraphVizDot

module internal DotToString =
    open DotAst

    type LabelEditor = string -> string

    let exportBoolean (value:bool) =
        match value with
            | true -> "true"
            | false -> "false"
    
    let exportShape (shape:Shape) =
        match shape with
            | Shape.Ellipse -> "ellipse"
            | Shape.Box -> "box"
            | Shape.None -> "none"

    let exportStyle (style:Style) =
        match style with
            | Style.Dashed -> "dashed"
            | Style.Solid -> "solid"
            | Style.Dotted -> "dotted"
            | Style.Bold -> "bold"
            | Style.Rounded -> "rounded"

    let exportDirection (direction:Direction) =
        match direction with
            | Direction.None -> "none"
            | Direction.Forward -> "forward"
            | Direction.Back -> "back"
            | Direction.Both -> "both"

    let exportRankdir (rankdir:Rankdir) =
        match rankdir with
            | Rankdir.LeftToRight -> "LR"
            | Rankdir.TopToBottom -> "TB"
            | Rankdir.RightToLeft -> "RL"
            | Rankdir.BottomToTop -> "BT"

    let exportAttribute (labelEditor:LabelEditor) (attribute:Attribute) =
        match attribute with
            | Attribute.Shape (shape) ->
                sprintf "shape=%s" (exportShape shape)
            | Attribute.Height (height) ->
                sprintf "height=%d" height
            | Attribute.Width (width) ->
                sprintf "width=%d" width
            | Attribute.Peripheries (peripheries) ->
                sprintf "peripheries=%d" peripheries
            | Attribute.Label (label) ->
                sprintf "label=\"%s\"" (labelEditor label)
            | Attribute.TexLabel (label) ->
                sprintf "texlbl=\"%s\"" (labelEditor label)
            | Attribute.ExternalLabel (xlabel) ->
                sprintf "xlabel=\"%s\"" (labelEditor xlabel)
            | Attribute.Fontsize (fontsize) ->
                sprintf "fontsize=%d" fontsize
            | Attribute.Fixedsize (fixedsize) ->
                sprintf "fixedsize=%s" (exportBoolean fixedsize)
            | Attribute.Direction (direction) ->
                sprintf "dir=%s" (exportDirection direction)
            | Attribute.Color (color) ->
                sprintf "color=%s" color
            | Attribute.Style (style) ->
                sprintf "style=%s" (exportStyle style)
            | Attribute.Tailclip (tailclip) ->
                sprintf "tailclip=%s" (exportBoolean tailclip)
            | Attribute.Headclip (headclip) ->
                sprintf "headclip=%s" (exportBoolean headclip)
            | Attribute.Fontname (fontname) ->
                sprintf "fontname=\"%s\"" fontname
            | Attribute.Rank (rank) ->
                sprintf "rank=%s" rank
            | Attribute.Rankdir (rankdir) ->
                sprintf "rankdir=%s" (exportRankdir rankdir)
            | Attribute.Ranksep (ranksep) ->
                sprintf "ranksep=%s" ranksep
            | Attribute.Resolution (resolution) ->
                sprintf "resolution=%d" resolution
                
    let exportAttributes (labelEditor:LabelEditor) (attributes:Attribute list) =
        if attributes.IsEmpty then
            ""
        else
            let attributeString = attributes |> List.map (exportAttribute labelEditor) |> String.concat ","
            sprintf " [%s]" attributeString
    
    let exportNodeDecl (labelEditor:LabelEditor) (nodeDecl:NodeDecl) =
        sprintf "%s%s;" nodeDecl.Node (exportAttributes labelEditor nodeDecl.Attributes)

    let exportTransitionDecl (labelEditor:LabelEditor) (transitionDecl:TransitionDecl) =
        sprintf "%s->%s%s;" transitionDecl.From transitionDecl.To (exportAttributes labelEditor transitionDecl.Attributes)

    let exportGroup (labelEditor:LabelEditor) (indent:int) (group:Group) =
        let indentAndNewline (str:string) = (String.replicate indent "\t") + str + "\n"
        let nodeAttributes =
            if group.NodeAttributes.IsEmpty then
                ""
            else
                sprintf "node%s;" (exportAttributes labelEditor group.NodeAttributes ) |> indentAndNewline
        let nodes =
            group.Nodes |> List.map (exportNodeDecl labelEditor)
                        |> List.map indentAndNewline
                        |> String.concat ""
        let transitions =
            group.Transitions |> List.map (exportTransitionDecl labelEditor)
                              |> List.map indentAndNewline
                              |> String.concat ""
        sprintf "%s%s%s" nodeAttributes nodes transitions


    let exportDigraph (labelEditor:LabelEditor) (digraph:Digraph) =
        assert (digraph.GraphAttributes.IsEmpty) //TODO
        let subGroups =
            let exportSubGroup group =
                sprintf "\t{\n%s\t}\n" (exportGroup labelEditor 2 group)
            digraph.SubGroups |> List.map exportSubGroup |> String.concat ""
        let mainGroup =
            exportGroup labelEditor 1 digraph.MainGroup
        sprintf "digraph %s {\n%s%s}" digraph.Name subGroups mainGroup

    
    let labelEditor_keepLabel : LabelEditor =
        let keepLabel (oldLabel:string) = oldLabel
        keepLabel
    
    // to plain dot-format (for export to pdf svg png...)
    let labelEditor_toUtf8 (str:string) =
        str.Replace("\\alpha","α")
           .Replace("\\beta","β")
           .Replace("\\phi","φ")
           .Replace("\\rightarrow","→")
           //TODO (maybe as own labelEditor): With Subscripts ₀₁₂₃₄₅₆₇₈₉₍₎
     
    let labelEditor_embedInMath =
        //  TODO: Embed \alpha, \phi,.. in Math environment. And \mathit
        labelEditor_keepLabel

    open SafetySharp.Workflow
        
    let exportDotPlainFile () 
            : ExogenousWorkflowFunction<Digraph,string> = workflow {
        let! digraph = getState ()
        let asString = exportDigraph labelEditor_keepLabel digraph
        do! updateState asString
    }
    