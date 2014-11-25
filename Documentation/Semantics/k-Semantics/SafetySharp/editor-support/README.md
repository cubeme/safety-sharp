# Syntax highlighting of .safetysharp files in vim/gvim

## Linux / OS X

1. Copy "safetysharp.vim" file into the "~/.vim/syntax" directory

2. Add the following to your ~/.vimrc file
```
au BufRead,BufNewFile *.safetysharp set filetype=safetysharp
au! Syntax safetysharp source safetysharp.vim
syn on
```

## Windows (gvim)

1. Copy "safetysharp.vim" file into the "C:\Program Files (x86)\Vim\vim74\syntax" directory

2. Add the following to your "C:\Program Files (x86)\Vim\_vimrc" file

```
au BufRead,BufNewFile *.safetysharp set filetype=safetysharp
au! Syntax safetysharp source safetysharp.vim
syn on
```
