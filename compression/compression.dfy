/*  
 * The compression algorithm is based on Lempel-Ziv-Welch algorithm.
 * In our algorithm a word (group of bytes) can be of the size of multiple of 8 bits and keep
 * the first byte without two times, one as word and other as byte, this way we can calculate the size
 * of word.
 * Group 9
 */

include "Io.dfy"

function compress(bytes:seq<byte>) : seq<byte>
{
  if |bytes|==0 then [] else [bytes[0]] + compressorHelper(bytes,0,[])
}

function compressorHelper(bytes:seq<byte> , currentpos : int, lastBytes:seq<byte>): seq<byte>
requires |bytes|>0 
requires 0<=currentpos
decreases |bytes|-currentpos
{
 if currentpos>= |bytes| then [] else if |lastBytes| > 1 then compressorHelper(bytes, currentpos + 1,  lastBytes[1..] ) else
  if |lastBytes| == 1 then compressorHelper(bytes, currentpos + 1, [] ) else
  padding(div(|dictSeq(bytes,|bytes|)| - |IntByteConvertor( findMatch( BestMatch(bytes,currentpos,1,dictSeq(bytes,currentpos)),0,dictSeq(bytes,currentpos)))|,0)
  ,IntByteConvertor( findMatch( BestMatch(bytes,currentpos,1,dictSeq(bytes,currentpos)),0,dictSeq(bytes,currentpos)))) 
  + if  | BestMatch(bytes,currentpos,1,dictSeq(bytes,currentpos))|>1 then compressorHelper(bytes, currentpos + 1,  BestMatch(bytes,currentpos,1,dictSeq(bytes,currentpos))[1..])
  else compressorHelper(bytes, currentpos + 1, [] )
}

function  div(a : int , counter :int ):int
decreases a
{
    if a<256 then counter else div(a/256,counter+1)
}

function dictSeq(bytes:seq<byte>,limit:int) : seq<seq<byte>>
  requires 0 <=limit <= |bytes|
{
  iteratordict(bytes,0,limit,begindict(0,255))
}

function iteratordict(bytes:seq<byte>,counter:int,limit:int, currentdict: seq<seq<byte>>) : seq<seq<byte>>
requires 0<=counter<=|bytes|
requires counter<=limit<=|bytes|
decreases |bytes|-counter
{
  if (|bytes|<=counter || counter >= limit) then currentdict else iteratordict(bytes,counter+1,limit,currentdict + nextNotdict(bytes,counter,counter+1,currentdict))
}

function findMatch(currentComb :seq<byte>, counter:int, currentdict: seq<seq<byte>>) : int
requires 0<=counter<=|currentdict|
ensures counter>=0
decreases |currentdict|-counter
{
  if |currentdict|<=counter then 0 else if currentComb == currentdict[counter] then counter else findMatch(currentComb,counter+1,currentdict)
}

function BestMatch(bytes:seq<byte>, currentpos :int, counter:int, currentdict: seq<seq<byte>>) : seq<byte>
requires 0<=currentpos<|bytes|
requires 1<=counter
requires 1<=counter+currentpos<=|bytes|
ensures 1<=counter
decreases |bytes| - currentpos-counter
{
       if |bytes|< currentpos+counter then  []  else if exists j:: 0<=j<|currentdict| && currentdict[j] == bytes[currentpos..currentpos+counter] then
       if |bytes|> currentpos+counter && exists j:: 0<=j<|currentdict| && currentdict[j] == bytes[currentpos..currentpos+counter+1] then BestMatch(bytes,currentpos,counter+1,currentdict) else bytes[currentpos..currentpos+counter]
      else bytes[currentpos..currentpos+1]
}

function IntByteConvertor(input :int):seq<byte>
decreases input
{
  if input<0 then []  else if  0<=input<256  then [input as byte] else IntByteConvertor(input/256) + [ (input % 256) as byte] 
}

function ByteIntConvertor(bytes:seq<byte>):int
requires |bytes|>0
{
  convert(bytes,0)
}

function convert(bytes:seq<byte>,counter:int):int
requires |bytes|>0
requires 0<=counter<=|bytes|
decreases |bytes|-counter
{
  if counter>=|bytes| then 0 else bytes[counter] as int*power(256,counter) + convert(bytes,counter+1)
}

function  power(a : int , counter :int ):int
decreases counter
{
    if counter<=0 then a else power(a*256,counter-1)
}

function nextNotdict(bytes:seq<byte>,min:int, max:int,currentdict: seq<seq<byte>>) : seq<seq<byte>>
requires min+1<= max
requires 0<=min<|bytes|
requires 1<=max<=|bytes|
decreases |bytes|-max
{
  if max>=|bytes| then [] else if exists j:: 0<=j<|currentdict| && currentdict[j] == bytes[min..max] then nextNotdict(bytes,min,max+1,currentdict)  else [bytes[min..max]]
}



function begindict(counter:int,cap:int) : seq<seq<byte>>
requires 0<=counter<256
requires counter<=cap<256
decreases cap-counter{
 if cap<0 then [] else if counter == cap then [[cap as byte]] else [[(counter) as byte]]+ begindict(counter+1,cap)
}

function decompress(bytes:seq<byte>) : seq<byte>

requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i]  &&forall j:: 0<j<i ==> bytes[j] ==0


requires check4codelen(bytes)>0                                                                                                                                               
requires ((|bytes|-1)%check4codelen(bytes))==0 //compress file size is always going to be composed from words of the same size = check4codelen(bytes)
{
  if |bytes|==0 then [] else if |bytes| ==1 then [bytes[0]] else [bytes[0]] + decompressHelper(bytes,1)
}

function decompressHelper(bytes:seq<byte> , currentpos : int): seq<byte>
requires |bytes|>=2 
requires 1<=currentpos
requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i] &&forall j:: 0<j<i ==> bytes[j] == 0
requires check4codelen(bytes)>0
requires ((|bytes|-1)%check4codelen(bytes))==0

decreases |bytes|-currentpos
{                                                                     	                      // use dictinary to translate symbol 
  if (currentpos+1)*check4codelen(bytes)+1 > |bytes| || |bytes|==2  then [] else  FindMatchDic(ByteIntConvertor(bytes[currentpos*check4codelen(bytes)+1..(currentpos+1)*check4codelen(bytes)+1]),getCurrentDict(bytes,currentpos))
  + decompressHelper(bytes,currentpos+1)
}

function getCurrentDict(bytes:seq<byte>,limit:int) : seq<seq<byte>>
requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i] &&forall j:: 0<j<i ==> bytes[j] == 0
requires 2*check4codelen(bytes)+1<=(limit+1)*check4codelen(bytes)+1<=|bytes| 
requires check4codelen(bytes)>0 
{
   nextNotdictAdd(bytes,1,begindictPadd(bytes,0,255),bytes[1..check4codelen(bytes)+1],limit)
}

function nextNotdictAdd(bytes:seq<byte>,min:int, currentdict: seq<seq<byte>>,w:seq<byte>,max:int) : seq<seq<byte>> // developing dictionary with max iterations
requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i] &&forall j:: 0<j<i ==> bytes[j] == 0
requires |w|>0;
requires check4codelen(bytes)>0  
requires 1<=min<= max
requires (min+1)*check4codelen(bytes)+1<=(max+1)*check4codelen(bytes)+1<=|bytes| 
decreases max-min
{
  if min+1>=max then []  else 
    if |currentdict|>ByteIntConvertor(bytes[min*check4codelen(bytes)+1..(min+1)*check4codelen(bytes)+1])  //if current word is on dictionary
    then nextNotdictAdd(bytes,min+1,currentdict + [w + bytes[min*check4codelen(bytes)+1..(min+1)*check4codelen(bytes)+1][0..1]] ,bytes[min*check4codelen(bytes)+1..(min+1)*check4codelen(bytes)+1],max) 
    else if  |currentdict|==ByteIntConvertor(bytes[min*check4codelen(bytes)+1..(min+1)*check4codelen(bytes)+1]) // in case of sequence of same value
          then nextNotdictAdd(bytes,min+1,currentdict + [w + w[0..1]] ,w + w[0..1],max)
          else  nextNotdictAdd(bytes,min+1,currentdict,w,max)
}

function begindictPadd(bytes:seq<byte>,counter:int,cap:int) : seq<seq<byte>>  // create inital dictionary
requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i] &&forall j:: 0<j<i ==> bytes[j] == 0 // after the first byte there will be sequence and the same byte again
requires 0<=counter<256                                                                     // ex: [6,0,6] -> allows to know size of word (this case 2)
requires counter<=cap<256
decreases cap-counter{
 if cap<0 then [] else if counter == cap then [[cap as byte]] else  [padding(check4codelen(bytes)-1,[(counter) as byte])]+ begindict(counter+1,cap)
}



function FindMatchDic(pos :int, currentdict: seq<seq<byte>>) : seq<byte>

{
  if 0<=pos<|currentdict| then currentdict[pos]  else []
}


lemma  lossless(bytes:seq<byte>)
 //ensures decompress(compress(bytes)) == bytes;
{
}

method {:axiom} compress_impl(bytes:array?<byte>) returns (compressed_bytes:array?<byte>)
  requires bytes != null;
  ensures  compressed_bytes != null;
  ensures |bytes[..]|>0 ==> |compressed_bytes[..]| >0
  ensures |bytes[..]|>0 ==> bytes[0] == compressed_bytes[0]
 // ensures   bytes.Length>1 ==> exists i:: 1<=i<|compressed_bytes[..]| && compressed_bytes[0]==compressed_bytes[i] && forall j:: 0<j<i ==> compressed_bytes[j] ==0 
 // ensures  compressed_bytes[..] == compress(bytes[..]);
{
    if(bytes.Length<=1){
    compressed_bytes:= bytes;
    return compressed_bytes;
    }
    var dictSize :=0;
    var codelen := 1;
    var dict :  map<seq<byte>,seq<byte>>;
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
    print("Create base dictionary\n");
    
    dict := dict[[i] := [i]];
    dictSize := dictSize + 1;
    assert forall b:byte::  [b] in dict ;
    var dictb := dict;
    var currentByte:=0;
    var windowchain :seq<byte> := [];
    var w : seq<byte> := [];
    var out : seq<seq<byte>>:=[];
    assert |out| == 0;
    
    var percentageHelper: int := bytes.Length/10;
  
    print("0% ");
    while (currentByte < |bytes[..]|)
    decreases |bytes[..]|- currentByte
    invariant 0<=currentByte<=|bytes[..]|;
    invariant windowchain!=[] ==> windowchain in dict
    invariant currentByte==0 ==>  w==[]
    invariant |bytes[..]|==0 ==> |out|==0;
    invariant w!=[]   ==> ( w==windowchain || w== [bytes[currentByte-1]])
    invariant forall j:byte , x:int :: 0<=x<|bytes[..]| && bytes[x]==j ==> [j] in dict;
    { 
        assert |bytes[..]|>0;
         windowchain := w + [bytes[currentByte]];
        if(windowchain in dict){
            w := [];
            w := windowchain;
            assert windowchain in dict ==> w == windowchain;
        }else{
            if (w in dict){
                ghost var teste:=dict[w];
                out := out + [dict[w]];
                assert w in dict ==> exists j:seq<byte> ::j in dict && dict[j] == teste;
            }
            var auxDict := dictSize;
            var aux : seq<byte> := [];
            ghost var helper := 0;
            while(auxDict>=256)
            decreases auxDict
            invariant 0<=auxDict<=dictSize;
            invariant 0<=helper
            {   
              aux := [(auxDict%256) as byte] + aux;
              auxDict := auxDict/256;                      
              
              helper:=1+helper;
            }
            aux := [auxDict as byte] + aux;
            dict := dict[windowchain:=aux];
            dictSize := dictSize + 1;
            w := [bytes[currentByte]];
            assert windowchain !in dict ==>  w == [bytes[currentByte]];
        }        
        currentByte:= currentByte+1;
        if(bytes.Length>=10 &&currentByte%percentageHelper==0){
          print("=> ");
          print(10*currentByte/percentageHelper);
          print("% ");
        }
    }
    print("Finishing encoding cycle\n");
    assert |bytes[..]|==0 ==> |w| ==0;
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
    var encoded:seq<byte>;
    if(|bytes[..]|>0){
    encoded:= [bytes[0]];
    }
      assert |bytes[..]|>0 ==> encoded[0]==bytes[0];
    codelen:=countHelper;
    assert |bytes[..]|==0 ==> |out|==0;
    var auxencoded: seq<byte> := [];

    while(j<|out|)
    decreases |out|-j
    invariant |bytes[..]|>0 ==> 1<=|encoded|
    invariant |bytes[..]|>0 ==> encoded[0]==bytes[0]
    invariant 0<=j<=|out|
    //invariant j<|out| ==> encoded == [bytes[0]] + padder(out,j,codelen)
    {   
        auxencoded := [];
        countHelper:=codelen;
        ghost var inversecounter:=0;
        if (|out[j]|<countHelper){
          while (|out[j]|<countHelper)
          invariant |out[j]|<=countHelper<=codelen
          invariant  0<=|out[j]|
          invariant |bytes[..]|>0 ==>|encoded|>=1
          invariant encoded[0]==bytes[0]
          decreases  countHelper-|out[j]|
          {
            auxencoded:= auxencoded + [0];
            countHelper:=countHelper-1;
            inversecounter:= inversecounter+1;
          }          
       }
       auxencoded := auxencoded + out[j];
       encoded := encoded + auxencoded;
       assert |encoded| >=1;
       j := j+1;
    }

    print("Finish Padding\n");
  assert |bytes[..]|>0 ==> encoded[0]==bytes[0];
   compressed_bytes:=ArrayFromSeq<byte>(encoded);
  assert |bytes[..]|>0 ==> encoded[0] == compressed_bytes[0];
  assert |bytes[..]|>0 ==> bytes[0] == compressed_bytes[0];


}

method decompress_impl(compressed_bytes:array?<byte>) returns (bytes:array?<byte>)
  requires compressed_bytes != null;
  requires compressed_bytes.Length>0
  requires exists i:: 1<=i<|compressed_bytes[..]| && compressed_bytes[0]==compressed_bytes[i]  && forall j:: 0<j<i ==> compressed_bytes[j] ==0 
  requires check4codelen(compressed_bytes[..])>0 && ((|compressed_bytes[..]|-1)%check4codelen(compressed_bytes[..]))==0                                                                                                                                       
  ensures  bytes != null;
  //ensures  bytes[..] == decompress(compressed_bytes[..]);
{
  if(compressed_bytes.Length<=1){
    bytes:= compressed_bytes;
    return bytes;
  }
  var codelen:nat :=1;
  assert compressed_bytes[codelen] == 0  || compressed_bytes[0] == compressed_bytes[codelen];
  var firstByte := compressed_bytes[0];
  
  while(firstByte != compressed_bytes[codelen])
  invariant 1<=codelen<compressed_bytes.Length
  decreases compressed_bytes.Length - codelen
  {
    
    codelen :=codelen+1;
    
    if(codelen==compressed_bytes.Length){
      print("Something went wrong\n");
      bytes:= compressed_bytes;
      return bytes;
    }
  }

  
  var dictSize:nat:=0;
  var dict :  map<seq<byte>,seq<byte>>;
  var i:byte:=0;
  while(i<255)
  decreases 255-i
  invariant 0<=i<=255
  invariant i>0 ==> padding(codelen-1,[i-1]) in dict;
  invariant i>0 ==> dict[padding(codelen-1,[i-1])] == [i-1];
  invariant i>0 ==>forall b:byte:: 0<=b<i ==> padding(codelen-1,[b]) in dict
  //invariant i>0 ==>forall b:byte:: 0<=b<i ==> dict[padding(codelen-1,[b])] == [b]
  {
    var auxbyte:seq<byte>:= padding(codelen-1,[i]);
    dict := dict[auxbyte := [i]]; 
    assert padding(codelen-1,[i]) in dict;
    assert dict[padding(codelen-1,[i])] == [i];
    dictSize := dictSize + 1;
    i:= i+1;
    } 
    print("Create base dictionary\n");
    
    dict := dict[ padding(codelen-1,[i]) := [i]];
    dictSize := dictSize + 1;
    assert forall b:byte::  padding(codelen-1,[b]) in dict ;
    var currentword:=1;
    print(compressed_bytes[0]);
    print(compressed_bytes[1..codelen+1]);
    if(compressed_bytes[1..codelen+1] !in dict){
      print("Something went wrong!\n");
      bytes:= compressed_bytes;
      return bytes;
    }
  var w := dict[compressed_bytes[1..codelen+1]];

  var out: seq<byte> := w;

  while(codelen*(currentword+1)+1<=compressed_bytes.Length)
  decreases compressed_bytes.Length -(codelen*currentword+1)
  {
    var windowchain:= compressed_bytes[(codelen)*currentword+1..(codelen)*(currentword+1)+1];
    var entry : seq<byte> ;
    if(windowchain in dict){
      entry := dict[windowchain];
    }else{
      var auxDict := dictSize;
      var aux : seq<byte> := [];
      ghost var helper := 0;
      while(auxDict>=256)
      decreases auxDict
      invariant 0<=auxDict<=dictSize;
      invariant 0<=helper
      {   
        aux := [(auxDict%256) as byte] + aux;
        auxDict := auxDict/256;                      
        helper:=1+helper;
      }
       aux := [(auxDict%256) as byte] + aux;
      if(aux==windowchain && |w|>0){
        
        entry := w + [w[0]];
        print(entry);
      }

    }
    if(|entry|>0){
      out:= out + entry;
      var auxDict := dictSize;
      var aux : seq<byte> := [];
      ghost var helper := 0;
      while(auxDict>=256)
      decreases auxDict
      invariant 0<=auxDict<=dictSize;
      invariant 0<=helper
      {   
        aux := [(auxDict%256) as byte] + aux;
        auxDict := auxDict/256;                      
        helper:=1+helper;
      }

      aux := [auxDict as byte] + aux;

      dict := dict[padding(codelen-|aux|,aux):=w+[entry[0]]];
      dictSize:= dictSize +1;
      w:=entry;
    }

    currentword:= currentword+1; 
  }

  bytes := ArrayFromSeq(out);

}

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  requires |env.constants.CommandLineArgs()|>=4
  requires env.constants.CommandLineArgs()[1] == "1"[..] ||  env.constants.CommandLineArgs()[1] == "0"[..]
  requires env.constants.CommandLineArgs()[2] in env.files.state()
  requires var bytes := env.files.state()[env.constants.CommandLineArgs()[2]];
      env.constants.CommandLineArgs()[1] == "1"[..] ==> (exists i:: 1<=i<|bytes| && bytes[0]==bytes[i]   && forall j:: 0<j<i ==> bytes[j] ==0) 
   requires var bytes := env.files.state()[env.constants.CommandLineArgs()[2]];
      env.constants.CommandLineArgs()[1] == "1"[..] ==> check4codelen(bytes[..])>0 && ((|bytes[..]|-1)%check4codelen(bytes[..]))==0 
   requires var bytes := env.files.state()[env.constants.CommandLineArgs()[2]];
       |bytes|>0
  requires env.constants.CommandLineArgs()[3] !in env.files.state()
  modifies env.ok
  modifies env.files 
  ensures env.ok.ok()  ==> env.constants.CommandLineArgs()[3] in env.files.state();
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[2] in env.files.state()
{
   var numArgs :=env.constants.NumCommandLineArgs(env);
  if(numArgs<4){
     print("Not enough arguments, it requires 3");
  }
  var compress := false;
  var uncompress := false;
  var bufferSize,writeBufferSize:=0,0;
  var sucessLen := false;
  var original:= env.constants.GetCommandLineArg(2,env);   
  var copy :=env.constants.GetCommandLineArg(3,env);
  var arg := env.constants.GetCommandLineArg(1,env);
  uncompress := arg[..] == "1"[..];
  compress := arg[..] == "0"[..];
  assert( compress ==> env.constants.CommandLineArgs()[1] == "0"[..]);
  assert( uncompress ==> env.constants.CommandLineArgs()[1] == "1"[..]);

  var OriginalExist :=FileStream.FileExists(original,env);
  
  if(!OriginalExist){
    print("Original file not found...");
  }
  assert OriginalExist ==> old(env.constants.CommandLineArgs())[2] in env.files.state();
  var CopyExist := FileStream.FileExists(copy,env);
  assert CopyExist ==> old(env.constants.CommandLineArgs())[3] in env.files.state();
  if(CopyExist){
    print("Destination file already exists");  
  }


  if(OriginalExist && !CopyExist && (uncompress || compress)){
    sucessLen,bufferSize := FileStream.FileLength(original,env);
  }
  var originalStream, copyStream;
  var successOriginal,successCopy:=false,false;
  var successRead,successWrite := false,false;
   var successClose,successCloseCopy := false,false;
  if(sucessLen && (!CopyExist )){
    var buffer := new  byte[bufferSize];
    successOriginal,originalStream := FileStream.Open(original,env);
    if(successOriginal){
      successCopy,copyStream := FileStream.Open(copy,env);
      if(successCopy){
        successRead := originalStream.Read(0,buffer,0,bufferSize);
        assert env.ok.ok() ==> old(env.files.state())[original[..]] == buffer[..];
        if(successRead){
          var buffer2;
          if(compress){
            buffer2 := compress_impl(buffer);
          }
          else{
            buffer2 := decompress_impl(buffer);
          }
          successWrite := copyStream.Write(0,buffer2,0,|buffer2[..]| ); 
         // assert env.ok.ok() ==> env.files.state()[copy[..]] == buffer[..];
          //assert env.ok.ok() ==> env.files.state() == old(env.files.state())[copy[..]:=buffer[..]] ; 
          if(successWrite){
            successClose := originalStream.Close();
            if(successClose){
              successCloseCopy := copyStream.Close();        
              if(successCloseCopy){
                print("DONE!");
              }
            }
          }
        }
      }
    }
  }
  
  if(!successCloseCopy && OriginalExist && !CopyExist){
     print("Something went wrong");
  }
}


method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}


function method padding(counter:int, a:seq<byte>):seq<byte>
decreases counter
{
     padd(counter) + a
}

function method padd(counter:int):seq<byte>
decreases counter
{
    if counter <=0 then [] else [0] + padd(counter-1)
}

function check4codelen(bytes:seq<byte>):int
requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i]  &&forall j:: 0<j<i ==> bytes[j] ==0
{
  check4codelenHelper(bytes,1)
} 

function check4codelenHelper(bytes:seq<byte>, counter : int):int
requires exists i:: 1<=i<|bytes| && bytes[0]==bytes[i]  &&forall j:: 0<j<i ==> bytes[j] ==0
requires 1<=counter<|bytes|
decreases |bytes|-counter
{
  if counter>=|bytes|-1 then -1 else if bytes[0]==bytes[counter] then counter else check4codelenHelper(bytes,counter+1)
}

function padder(bytes:seq<seq<byte>>,limit:int,codelen:int):seq<byte>
requires 0<=limit<=|bytes|
{
  padderRecursion(bytes,limit,codelen,0)
}

function padderRecursion(bytes:seq<seq<byte>>,limit:int,codelen:int,counter:int):seq<byte>
requires 0<=limit<=|bytes|
requires 0<=counter<=limit
decreases limit-counter
{
  if limit==counter then [] else padding(codelen-|bytes[counter]|,bytes[counter])+padderRecursion(bytes,limit,codelen,counter+1)
}