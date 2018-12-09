/*
 * Implementation of lzw in dafny
 *
 * 
 */
include "Io.dfy"

method compress(input: array<byte>  ) returns (encoded: array<byte>)
    
{   
    var dictSize :=0;
    var codelen := 1;
    var dict :  map<seq<byte>,seq<byte>>;
    ghost var dictHelper:  map<seq<byte>,seq<byte>> := dict;
    var i:byte:=0;
    while(i<255)
    decreases 255-i
    invariant 0<=i<=255
    invariant i>0 ==> [i-1] in dict;
    invariant i>0 ==>forall b:byte:: 0<=b<i ==> [b] in dict
    invariant i>0 ==>forall b:byte:: 0<=b<i ==> dict[[b]] == [b]
    {
        dict := dict[[i] := [i]];
        assert [i] in dict;
        dictSize := dictSize + 1;
        i:= i+1;
    } 
    dict := dict[[i] := [i]];
    assert forall b:byte::  [b] in dict ;
    var dictb := dict;
    var currentByte:=0;
    var windowchain :seq<byte> := [];
    var w : seq<byte> := [];
    var out : seq<seq<byte>>;
    while (currentByte < |input[..]|)
    decreases |input[..]|- currentByte
    invariant 0<=currentByte<=|input[..]|;
    invariant windowchain!=[] ==> windowchain in dict
    invariant currentByte==0 ==>  w==[]
    invariant w!=[] && currentByte>0  ==> ( w==windowchain || w== [input[currentByte-1]])
    invariant forall j:byte , x:int :: 0<=x<|input[..]| && input[x]==j ==> [j] in dict;
    {
         windowchain := w + [input[currentByte]];
        if(windowchain in dict){
            w := [];
            w := windowchain;
        }else{
            if (w in dict){
                out := [dict[w]];
            }
            var auxDict := dictSize;
            var aux : seq<byte>;
            ghost var helper := 0;
            while(auxDict>=256)
            decreases auxDict
            invariant 0<=auxDict<=dictSize;
            invariant 0<=helper
            {
                var aux2:= auxDict;
                while(aux2>=256)
                invariant 0<=aux2<=auxDict; 
                decreases aux2
                {
                    aux2 := aux2/256;  
                               
                } 
                
                assert aux2 <256;

                aux := aux + [aux2 as byte];
                auxDict := auxDict % 256;
                helper:=1+helper;
            }
            aux := aux + [auxDict as byte];
            dict := dict[windowchain:=aux];
            dictSize := dictSize + 1;
            w := [input[currentByte]];
        }
        
        currentByte:= currentByte+1;
    }
    if(|w| != 0){
        out:= out + [dict[w]];
    }
    var cal := dictSize; 
    var countHelper :=1;
    while(cal>=256)
    decreases cal
    {
        cal := cal/256;
        countHelper := countHelper+1;
    }
    var j:= 0;
    //while(j<|out|){
       // if (|out[j]|<countHelper){
           
     //   }
       //encoded := encoded +  
    //}



}

method decompress(input: array?<byte> ) returns (decompressed: array?<byte>){
    var codelen := 1;
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


function  heplerCalculation(a : int , counter :int):int
decreases counter
{
    if counter<=0 then a  else heplerCalculation(a % if power2(a,256)==0 then 256 else power2(a,256),counter-1)
}


function  power(a : int , counter :int ):int
decreases counter
{
    if counter<=0 then a else power(a*256,counter-1)
}

function  power2(a : int , counter :int ):int
requires counter>0
decreases a-counter
{
    if a<counter*256 then counter else power2(a,counter*256)
}


function  div(a : int , counter :int ):int
decreases counter
{
    if counter<=0 then a else div(a/256,counter-1)
}

function  div2(a : int , counter :int ):int
decreases a
{
    if a<256 then counter else div(a/256,counter+1)
}

method generateDictionary()returns (dict : seq<seq<byte>>)
ensures |dict|==256 ==> forall b:byte ::  dict[b] == [b]
{   
    var i:byte :=0;
    var arrayDict := new seq<byte>[256];
    while(i<255)
    decreases 255-i
    invariant 0<=i<=255
    invariant i>0 ==>forall b:byte:: 0<=b<i ==> arrayDict[b] == [b]
    {  
        arrayDict[i]:=[i];
        i:= i+1;
    } 
    arrayDict[i]:=[i];
    assert |arrayDict[..]| == 256;
    assert forall b:byte ::  arrayDict[..][b] == [b];
    dict := arrayDict[..];
    assert forall b:byte ::  dict[b] == [b];
}
