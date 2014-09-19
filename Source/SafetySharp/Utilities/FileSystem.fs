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

namespace SafetySharp.Internal.Utilities

open System.IO
open System.Text

/// Provides helper methods for working with the file system.
module internal FileSystem =

    /// Writes the given text to the file indicated by the path, using the given text encoding. If the file or some directories of
    /// the path do not exist, they are created. Otherwise, the contents of the file are overwritten.
    let WriteToFile path text encoding =    
        Directory.CreateDirectory (Path.GetDirectoryName path) |> ignore
        File.WriteAllText (path, text, encoding)

    /// Writes the given text to the file indicated by the path, using the ASCII encoding. If the file or some directories of
    /// the path do not exist, they are created. Otherwise, the contents of the file are overwritten.
    let WriteToAsciiFile path text =
        WriteToFile path text Encoding.ASCII
        
    [<RequireQualifiedAccess>]
    type MachineType =
        | AMD64
        | I386
        | Unknown 
        | Other of Type:uint16
            with
                override this.ToString() : string =
                    match this with
                        | AMD64 -> "AMD64"
                        | I386 -> "I386"
                        | _ -> "unknown"

    let GetDllMachineType  (dllPath:string) =
        // Source: http://stackoverflow.com/questions/1001404/check-if-unmanaged-dll-is-32-bit-or-64-bit/1002672#1002672
        //see http://www.microsoft.com/whdc/system/platform/firmware/PECOFF.mspx
        let fs = new FileStream(dllPath, FileMode.Open, FileAccess.Read)
        let br = new BinaryReader(fs)
        fs.Seek(int64(0x3c), SeekOrigin.Begin) |> ignore
        let peOffset = br.ReadInt32()
        fs.Seek(int64(peOffset), SeekOrigin.Begin) |> ignore
        let peHead = br.ReadUInt32();
        if peHead <> uint32(0x00004550)  then 
            // "PE\0\0", little-endian
            failwith "Can't find PE header"
        let machineTypeAsUint16 = br.ReadUInt16()
        br.Close()
        fs.Close()
        match int(machineTypeAsUint16) with
            | 0x8664 -> MachineType.AMD64
            | 0x14c ->  MachineType.I386
            | 0x0 -> MachineType.Unknown
            | _ -> MachineType.Other(machineTypeAsUint16)
    