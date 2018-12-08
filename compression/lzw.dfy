/*
 * Implementation of lzw in dafny
 *
 * 
 */
include "Io.dfy"

method compress(input: array?<byte>  ) returns (encoded: array?<byte>)
    
{   
    var dict :  map<seq<byte>,seq<byte>>;
    var i :=0;
    while(i<256)
    decreases 256-i
    invariant 0<=i<=256
    {
        var entry := new byte[1];
        entry[0] := i as byte;
        dict := dict[entry[..] := entry[..]];
        i:= i+1;
    }



}

method decompress(input: array?<byte> ) returns (decompressed: array?<byte>){

    var dict :  map<seq<byte>,seq<byte>>;
    var i :=0;
    while(i<256)
    decreases 256-i
    invariant 0<=i<=256
    {
        var entry := new byte[1];
        entry[0] := i as byte;
        dict := dict[entry[..] := entry[..]];
        i:= i+1;
    }
    
    
}

