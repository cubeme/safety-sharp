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

module DotAst =
    open SafetySharp

    // see http://www.graphviz.org/doc/info/attrs.html
    
    [<RequireQualifiedAccessAttribute>]
    type Shape =
        | Ellipse
        | Box
        | None
        
    [<RequireQualifiedAccessAttribute>]
    type Style =
        | Dashed
        | Solid
        | Dotted
        | Bold
        | Rounded // only for nodes, not for edges
        
    [<RequireQualifiedAccessAttribute>]
    type Direction =
        | None
        | Forward
        | Back
        | Both
        
    [<RequireQualifiedAccessAttribute>]
    type Rankdir =
        | LeftToRight
        | TopToBottom
        | RightToLeft
        | BottomToTop

    type Attribute =
        | Shape of Shape
        | Height of int
        | Width of int
        | Peripheries of int
        | Label of string
        | ExternalLabel of string
        | Fontsize of int
        | Fixedsize of bool
        | Direction of Direction
        | Color of string
        | Style of Style
        | Tailclip of bool
        | Headclip of bool
        | Fontname of string
        | Rank of string
        | Rankdir of Rankdir
        | Ranksep of string
        | Resolution of int //DPIs

    type Node = string
    
    type NodeDecl = {
        Node:Node;        
        Attributes:Attribute list;
    }

    type TransitionDecl = {
        From:Node;
        To:Node;
        Attributes:Attribute list;
    }

    type Group = {
        NodeAttributes:Attribute list;
        //TransitionAttributes:Attribute list;
        Nodes : NodeDecl list;
        Transitions : TransitionDecl list;
    }

    type Digraph = {
        Name:string;
        GraphAttributes:Attribute list;
        MainGroup:Group;
        SubGroups :Group list;
    }