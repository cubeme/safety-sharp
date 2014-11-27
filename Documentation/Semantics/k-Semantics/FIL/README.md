# Examples

You can find examples in [\Examples\FIL](https://github.com/isse-augsburg/safety-sharp/tree/master/Examples/FIL).

You can create a symbolic link for more convenience when trying out one of the semantics: 

* ```ln -s Examples ../../../../../Examples/FIL``` (Linux) 
* ```mklink /d Examples ..\..\..\..\..\Examples\FIL``` (Windows)


# How to work with k-Semantics
1. Download and install the k-Framework from http://www.kframework.org/ or https://github.com/kframework/k
2. Make sure path to fil.k is not to long and does not contain any white spaces or special characters
2. Compile the semantics in this folder  ```kompile fil.k```
3. Run an example ```krun simpleArithmetical1.fil```
4. Generate the PDF-Docu ```kompile fil.k --backend latex; pdflatex fil.tex```. For printing remove the posters-option from the tex-file. Option "tight" might lead to better results (see k.sty)
5. Search for all final states of a program (useful to evaluate guarded commands) ```krun  --search-final simpleGuardedCommands4.fil```