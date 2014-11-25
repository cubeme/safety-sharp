" Vim syntax file
" Language:      SafetySharp <https://github.com/isse-augsburg/safety-sharp>
" Maintainers:   Johannes Leupolz
" <johannes.leupolz@informatik.uni-augsburg.de>
" Inspired from, and reusing most of the k-Framework and Maude files.
" Below are the old copyright notices:
"
" Language:      K <k-framework.org>
" Maintainers:   Andrei Ștefănescu <stefane1@illinois.edu>
"                Traian Florin Șerbănuță <tserban2@illinois.edu>
"
" Language:      Maude <http://maude.cs.uiuc.edu/>
" Maintainer:    Steven N. Severinghaus <sns@severinghaus.org>
" Last Modified: 2005-02-03
" Version: 0.1
"
" To install, copy (or link) this file into the ~/.vim/syntax directory and add
" the following to the ~/.vimrc file
"
" au BufRead,BufNewFile *.k set filetype=safetysharp
" syn on


" Quit if syntax file is already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

command! -nargs=+ SafetySharpHiLink hi def link <args>

syn keyword safetySharpBoolean      true false
syn keyword safetySharpNumber       "\<\(\d\+\)[lL]\=\>"

syn match   safetySharpBinding       "<-i-"
syn match   safetySharpBinding       "<-d-"

syn match   safetySharpOperator      "|||" "||" "&&" "<" "<="
syn keyword safetySharpType          int bool

syn keyword safetySharpComponent     component
syn keyword safetySharpBehaviour     behaviour
 
SafetySharpHiLink safetySharpBoolean        Boolean
SafetySharpHiLink safetySharpNumber         Number
SafetySharpHiLink safetySharpBinding        Operator
SafetySharpHiLink safetySharpOperator       Operator
SafetySharpHiLink safetySharpType           Type
SafetySharpHiLink safetySharpComponent      Type
SafetySharpHiLink safetySharpBehaviour      Type

delcommand SafetySharpHiLink
  
let b:current_syntax = "safetysharp"

"EOF vim: tw=78:ft=vim:ts=8

