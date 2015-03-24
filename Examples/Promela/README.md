
## How to execute the FFB-Example:

You need Spin (http://spinroot.com and the gcc-compiler of MinGW). Make sure gcc.exe is in the PATH-Environment. (Search for "path environment variable windows" if you do not know how.)

##
```
> spin.exe -a ffb.pml
> gcc.exe  -DSAFETY  -o pan pan.c
> pan.exe  -m10000 -X
> spin.exe -g -l -p -r -s -t -X -u8000 ffb.pml
```