// Dafny program the program compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.2.0.10923
// Command Line Options: .\compression.dfy .\Io.dfy .\IoNative.cs
// the program

function compress(bytes: seq<byte>): seq<byte>
  decreases bytes
{
  if |bytes| == 0 then
    []
  else
    [bytes[0]] + compressorHelper(bytes, 0, [])
}

function compressorHelper(bytes: seq<byte>, currentpos: int, lastBytes: seq<byte>): seq<byte>
  requires |bytes| > 0
  requires 0 <= currentpos
  decreases |bytes| - currentpos
{
  if currentpos >= |bytes| then
    []
  else if |lastBytes| > 1 then
    compressorHelper(bytes, currentpos + 1, lastBytes[1..])
  else if |lastBytes| == 1 then
    compressorHelper(bytes, currentpos + 1, [])
  else
    padding(div(|dictSeq(bytes, |bytes|)| - |IntByteConvertor(findMatch(BestMatch(bytes, currentpos, 1, dictSeq(bytes, currentpos)), 0, dictSeq(bytes, currentpos)))|, 0), IntByteConvertor(findMatch(BestMatch(bytes, currentpos, 1, dictSeq(bytes, currentpos)), 0, dictSeq(bytes, currentpos)))) + if |BestMatch(bytes, currentpos, 1, dictSeq(bytes, currentpos))| > 1 then compressorHelper(bytes, currentpos + 1, BestMatch(bytes, currentpos, 1, dictSeq(bytes, currentpos))[1..]) else compressorHelper(bytes, currentpos + 1, [])
}

function div(a: int, counter: int): int
  decreases a
{
  if a < 256 then
    counter
  else
    div(a / 256, counter + 1)
}

function dictSeq(bytes: seq<byte>, limit: int): seq<seq<byte>>
  requires 0 <= limit <= |bytes|
  decreases bytes, limit
{
  iteratordict(bytes, 0, limit, begindict(0, 255))
}

function iteratordict(bytes: seq<byte>, counter: int, limit: int, currentdict: seq<seq<byte>>): seq<seq<byte>>
  requires 0 <= counter <= |bytes|
  requires counter <= limit <= |bytes|
  decreases |bytes| - counter
{
  if |bytes| <= counter || counter >= limit then
    currentdict
  else
    iteratordict(bytes, counter + 1, limit, currentdict + nextNotdict(bytes, counter, counter + 1, currentdict))
}

function findMatch(currentComb: seq<byte>, counter: int, currentdict: seq<seq<byte>>): int
  requires 0 <= counter <= |currentdict|
  ensures counter >= 0
  decreases |currentdict| - counter
{
  if |currentdict| <= counter then
    0
  else if currentComb == currentdict[counter] then
    counter
  else
    findMatch(currentComb, counter + 1, currentdict)
}

function BestMatch(bytes: seq<byte>, currentpos: int, counter: int, currentdict: seq<seq<byte>>): seq<byte>
  requires 0 <= currentpos < |bytes|
  requires 1 <= counter
  requires 1 <= counter + currentpos <= |bytes|
  ensures 1 <= counter
  decreases |bytes| - currentpos - counter
{
  if |bytes| < currentpos + counter then
    []
  else if exists j: int :: 0 <= j < |currentdict| && currentdict[j] == bytes[currentpos .. currentpos + counter] then
    if |bytes| > currentpos + counter && exists j: int :: 0 <= j < |currentdict| && currentdict[j] == bytes[currentpos .. currentpos + counter + 1] then
      BestMatch(bytes, currentpos, counter + 1, currentdict)
    else
      bytes[currentpos .. currentpos + counter]
  else
    bytes[currentpos .. currentpos + 1]
}

function IntByteConvertor(input: int): seq<byte>
  decreases input
{
  if input < 0 then
    []
  else if 0 <= input < 256 then
    [input as byte]
  else
    IntByteConvertor(input / 256) + [(input % 256) as byte]
}

function ByteIntConvertor(bytes: seq<byte>): int
  requires |bytes| > 0
  decreases bytes
{
  convert(bytes, 0)
}

function convert(bytes: seq<byte>, counter: int): int
  requires |bytes| > 0
  requires 0 <= counter <= |bytes|
  decreases |bytes| - counter
{
  if counter >= |bytes| then
    0
  else
    bytes[counter] as int * power(256, counter) + convert(bytes, counter + 1)
}

function power(a: int, counter: int): int
  decreases counter
{
  if counter <= 0 then
    a
  else
    power(a * 256, counter - 1)
}

function nextNotdict(bytes: seq<byte>, min: int, max: int, currentdict: seq<seq<byte>>): seq<seq<byte>>
  requires min + 1 <= max
  requires 0 <= min < |bytes|
  requires 1 <= max <= |bytes|
  decreases |bytes| - max
{
  if max >= |bytes| then
    []
  else if exists j: int :: 0 <= j < |currentdict| && currentdict[j] == bytes[min .. max] then
    nextNotdict(bytes, min, max + 1, currentdict)
  else
    [bytes[min .. max]]
}

function begindict(counter: int, cap: int): seq<seq<byte>>
  requires 0 <= counter < 256
  requires counter <= cap < 256
  decreases cap - counter
{
  if cap < 0 then
    []
  else if counter == cap then
    [[cap as byte]]
  else
    [[counter as byte]] + begindict(counter + 1, cap)
}

function decompress(bytes: seq<byte>): seq<byte>
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires check4codelen(bytes) > 0
  requires (|bytes| - 1) % check4codelen(bytes) == 0
  decreases bytes
{
  if |bytes| == 0 then
    []
  else if |bytes| == 1 then
    [bytes[0]]
  else
    [bytes[0]] + decompressHelper(bytes, 1)
}

function decompressHelper(bytes: seq<byte>, currentpos: int): seq<byte>
  requires |bytes| >= 2
  requires 1 <= currentpos
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires check4codelen(bytes) > 0
  requires (|bytes| - 1) % check4codelen(bytes) == 0
  decreases |bytes| - currentpos
{
  if (currentpos + 1) * check4codelen(bytes) + 1 > |bytes| || |bytes| == 2 then
    []
  else
    FindMatchDic(ByteIntConvertor(bytes[currentpos * check4codelen(bytes) + 1 .. (currentpos + 1) * check4codelen(bytes) + 1]), getCurrentDict(bytes, currentpos)) + decompressHelper(bytes, currentpos + 1)
}

function getCurrentDict(bytes: seq<byte>, limit: int): seq<seq<byte>>
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires 2 * check4codelen(bytes) + 1 <= (limit + 1) * check4codelen(bytes) + 1 <= |bytes|
  requires check4codelen(bytes) > 0
  decreases bytes, limit
{
  nextNotdictAdd(bytes, 1, begindictPadd(bytes, 0, 255), bytes[1 .. check4codelen(bytes) + 1], limit)
}

function nextNotdictAdd(bytes: seq<byte>, min: int, currentdict: seq<seq<byte>>, w: seq<byte>, max: int): seq<seq<byte>>
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires |w| > 0
  requires check4codelen(bytes) > 0
  requires 1 <= min <= max
  requires (min + 1) * check4codelen(bytes) + 1 <= (max + 1) * check4codelen(bytes) + 1 <= |bytes|
  decreases max - min
{
  if min + 1 >= max then
    []
  else if |currentdict| > ByteIntConvertor(bytes[min * check4codelen(bytes) + 1 .. (min + 1) * check4codelen(bytes) + 1]) then
    nextNotdictAdd(bytes, min + 1, currentdict + [w + bytes[min * check4codelen(bytes) + 1 .. (min + 1) * check4codelen(bytes) + 1][0 .. 1]], bytes[min * check4codelen(bytes) + 1 .. (min + 1) * check4codelen(bytes) + 1], max)
  else if |currentdict| == ByteIntConvertor(bytes[min * check4codelen(bytes) + 1 .. (min + 1) * check4codelen(bytes) + 1]) then
    nextNotdictAdd(bytes, min + 1, currentdict + [w + w[0 .. 1]], w + w[0 .. 1], max)
  else
    nextNotdictAdd(bytes, min + 1, currentdict, w, max)
}

function begindictPadd(bytes: seq<byte>, counter: int, cap: int): seq<seq<byte>>
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires 0 <= counter < 256
  requires counter <= cap < 256
  decreases cap - counter
{
  if cap < 0 then
    []
  else if counter == cap then
    [[cap as byte]]
  else
    [padding(check4codelen(bytes) - 1, [counter as byte])] + begindict(counter + 1, cap)
}

function FindMatchDic(pos: int, currentdict: seq<seq<byte>>): seq<byte>
  decreases pos, currentdict
{
  if 0 <= pos < |currentdict| then
    currentdict[pos]
  else
    []
}

lemma lossless(bytes: seq<byte>)
  decreases bytes
{
}

method {:axiom} compress_impl(bytes: array?<byte>) returns (compressed_bytes: array?<byte>)
  requires bytes != null
  ensures compressed_bytes != null
  ensures |bytes[..]| > 0 ==> |compressed_bytes[..]| > 0
  ensures |bytes[..]| > 0 ==> bytes[0] == compressed_bytes[0]
  decreases bytes
{
  if bytes.Length <= 1 {
    compressed_bytes := bytes;
    return compressed_bytes;
  }
  var dictSize := 0;
  var codelen := 1;
  var dict: map<seq<byte>, seq<byte>>;
  var i: byte := 0;
  while i < 255
    invariant 0 <= i <= 255
    invariant i > 0 ==> [i - 1] in dict
    invariant i > 0 ==> forall b: byte :: 0 <= b < i ==> [b] in dict
    invariant i > 0 ==> forall b: byte :: 0 <= b < i ==> dict[[b]] == [b]
    decreases 255 - i
  {
    dict := dict[[i] := [i]];
    assert [i] in dict;
    dictSize := dictSize + 1;
    i := i + 1;
  }
  print ""Create base dictionary\n"";
  dict := dict[[i] := [i]];
  dictSize := dictSize + 1;
  assert forall b: byte :: [b] in dict;
  var dictb := dict;
  var currentByte := 0;
  var windowchain: seq<byte> := [];
  var w: seq<byte> := [];
  var out: seq<seq<byte>> := [];
  assert |out| == 0;
  var percentageHelper: int := bytes.Length / 10;
  print ""0% "";
  while currentByte < |bytes[..]|
    invariant 0 <= currentByte <= |bytes[..]|
    invariant windowchain != [] ==> windowchain in dict
    invariant currentByte == 0 ==> w == []
    invariant |bytes[..]| == 0 ==> |out| == 0
    invariant w != [] ==> w == windowchain || w == [bytes[currentByte - 1]]
    invariant forall j: byte, x: int :: 0 <= x < |bytes[..]| && bytes[x] == j ==> [j] in dict
    decreases |bytes[..]| - currentByte
  {
    assert |bytes[..]| > 0;
    windowchain := w + [bytes[currentByte]];
    if windowchain in dict {
      w := [];
      w := windowchain;
      assert windowchain in dict ==> w == windowchain;
    } else {
      if w in dict {
        ghost var teste := dict[w];
        out := out + [dict[w]];
        assert w in dict ==> exists j: seq<byte> :: j in dict && dict[j] == teste;
      }
      var auxDict := dictSize;
      var aux: seq<byte> := [];
      ghost var helper := 0;
      while auxDict >= 256
        invariant 0 <= auxDict <= dictSize
        invariant 0 <= helper
        decreases auxDict
      {
        aux := [(auxDict % 256) as byte] + aux;
        auxDict := auxDict / 256;
        helper := 1 + helper;
      }
      aux := [auxDict as byte] + aux;
      dict := dict[windowchain := aux];
      dictSize := dictSize + 1;
      w := [bytes[currentByte]];
      assert windowchain !in dict ==> w == [bytes[currentByte]];
    }
    currentByte := currentByte + 1;
    if bytes.Length >= 10 && currentByte % percentageHelper == 0 {
      print ""=> "";
      print 10 * currentByte / percentageHelper;
      print ""% "";
    }
  }
  print ""Finishing encoding cycle\n"";
  assert |bytes[..]| == 0 ==> |w| == 0;
  if |w| != 0 {
    out := out + [dict[w]];
  }
  var cal := dictSize;
  var countHelper := 1;
  while cal >= 256
    decreases cal
  {
    cal := cal / 256;
    countHelper := countHelper + 1;
  }
  var j := 0;
  var encoded: seq<byte>;
  if |bytes[..]| > 0 {
    encoded := [bytes[0]];
  }
  assert |bytes[..]| > 0 ==> encoded[0] == bytes[0];
  codelen := countHelper;
  assert |bytes[..]| == 0 ==> |out| == 0;
  var auxencoded: seq<byte> := [];
  while j < |out|
    invariant |bytes[..]| > 0 ==> 1 <= |encoded|
    invariant |bytes[..]| > 0 ==> encoded[0] == bytes[0]
    invariant 0 <= j <= |out|
    decreases |out| - j
  {
    auxencoded := [];
    countHelper := codelen;
    ghost var inversecounter := 0;
    if |out[j]| < countHelper {
      while |out[j]| < countHelper
        invariant |out[j]| <= countHelper <= codelen
        invariant 0 <= |out[j]|
        invariant |bytes[..]| > 0 ==> |encoded| >= 1
        invariant encoded[0] == bytes[0]
        decreases countHelper - |out[j]|
      {
        auxencoded := auxencoded + [0];
        countHelper := countHelper - 1;
        inversecounter := inversecounter + 1;
      }
    }
    auxencoded := auxencoded + out[j];
    encoded := encoded + auxencoded;
    assert |encoded| >= 1;
    j := j + 1;
  }
  print ""Finish Padding\n"";
  assert |bytes[..]| > 0 ==> encoded[0] == bytes[0];
  compressed_bytes := ArrayFromSeq<byte>(encoded);
  assert |bytes[..]| > 0 ==> encoded[0] == compressed_bytes[0];
  assert |bytes[..]| > 0 ==> bytes[0] == compressed_bytes[0];
}

method decompress_impl(compressed_bytes: array?<byte>) returns (bytes: array?<byte>)
  requires compressed_bytes != null
  requires compressed_bytes.Length > 0
  requires exists i: int :: 1 <= i < |compressed_bytes[..]| && compressed_bytes[0] == compressed_bytes[i] && forall j: int :: 0 < j < i ==> compressed_bytes[j] == 0
  requires check4codelen(compressed_bytes[..]) > 0 && (|compressed_bytes[..]| - 1) % check4codelen(compressed_bytes[..]) == 0
  ensures bytes != null
  decreases compressed_bytes
{
  if compressed_bytes.Length <= 1 {
    bytes := compressed_bytes;
    return bytes;
  }
  var codelen: nat := 1;
  assert compressed_bytes[codelen] == 0 || compressed_bytes[0] == compressed_bytes[codelen];
  var firstByte := compressed_bytes[0];
  while firstByte != compressed_bytes[codelen]
    invariant 1 <= codelen < compressed_bytes.Length
    decreases compressed_bytes.Length - codelen
  {
    codelen := codelen + 1;
    if codelen == compressed_bytes.Length {
      print ""Something went wrong\n"";
      bytes := compressed_bytes;
      return bytes;
    }
  }
  var dictSize: nat := 0;
  var dict: map<seq<byte>, seq<byte>>;
  var i: byte := 0;
  while i < 255
    invariant 0 <= i <= 255
    invariant i > 0 ==> padding(codelen - 1, [i - 1]) in dict
    invariant i > 0 ==> dict[padding(codelen - 1, [i - 1])] == [i - 1]
    invariant i > 0 ==> forall b: byte :: 0 <= b < i ==> padding(codelen - 1, [b]) in dict
    decreases 255 - i
  {
    var auxbyte: seq<byte> := padding(codelen - 1, [i]);
    dict := dict[auxbyte := [i]];
    assert padding(codelen - 1, [i]) in dict;
    assert dict[padding(codelen - 1, [i])] == [i];
    dictSize := dictSize + 1;
    i := i + 1;
  }
  print ""Create base dictionary\n"";
  dict := dict[padding(codelen - 1, [i]) := [i]];
  dictSize := dictSize + 1;
  assert forall b: byte :: padding(codelen - 1, [b]) in dict;
  var currentword := 1;
  print compressed_bytes[0];
  print compressed_bytes[1 .. codelen + 1];
  if compressed_bytes[1 .. codelen + 1] !in dict {
    print ""Something went wrong!\n"";
    bytes := compressed_bytes;
    return bytes;
  }
  var w := dict[compressed_bytes[1 .. codelen + 1]];
  var out: seq<byte> := w;
  while codelen * (currentword + 1) + 1 <= compressed_bytes.Length
    decreases compressed_bytes.Length - (codelen * currentword + 1)
  {
    var windowchain := compressed_bytes[codelen * currentword + 1 .. codelen * (currentword + 1) + 1];
    var entry: seq<byte>;
    if windowchain in dict {
      entry := dict[windowchain];
    } else {
      var auxDict := dictSize;
      var aux: seq<byte> := [];
      ghost var helper := 0;
      while auxDict >= 256
        invariant 0 <= auxDict <= dictSize
        invariant 0 <= helper
        decreases auxDict
      {
        aux := [(auxDict % 256) as byte] + aux;
        auxDict := auxDict / 256;
        helper := 1 + helper;
      }
      aux := [(auxDict % 256) as byte] + aux;
      if aux == windowchain && |w| > 0 {
        entry := w + [w[0]];
        print entry;
      }
    }
    if |entry| > 0 {
      out := out + entry;
      var auxDict := dictSize;
      var aux: seq<byte> := [];
      ghost var helper := 0;
      while auxDict >= 256
        invariant 0 <= auxDict <= dictSize
        invariant 0 <= helper
        decreases auxDict
      {
        aux := [(auxDict % 256) as byte] + aux;
        auxDict := auxDict / 256;
        helper := 1 + helper;
      }
      aux := [auxDict as byte] + aux;
      dict := dict[padding(codelen - |aux|, aux) := w + [entry[0]]];
      dictSize := dictSize + 1;
      w := entry;
    }
    currentword := currentword + 1;
  }
  bytes := ArrayFromSeq(out);
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  requires |env.constants.CommandLineArgs()| >= 4
  requires env.constants.CommandLineArgs()[1] == ""1""[..] || env.constants.CommandLineArgs()[1] == ""0""[..]
  requires env.constants.CommandLineArgs()[2] in env.files.state()
  requires var bytes: seq<byte> := env.files.state()[env.constants.CommandLineArgs()[2]]; env.constants.CommandLineArgs()[1] == ""1""[..] ==> exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires var bytes: seq<byte> := env.files.state()[env.constants.CommandLineArgs()[2]]; env.constants.CommandLineArgs()[1] == ""1""[..] ==> check4codelen(bytes[..]) > 0 && (|bytes[..]| - 1) % check4codelen(bytes[..]) == 0
  requires var bytes: seq<byte> := env.files.state()[env.constants.CommandLineArgs()[2]]; |bytes| > 0
  requires env.constants.CommandLineArgs()[3] !in env.files.state()
  modifies env.ok, env.files
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[3] in env.files.state()
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[2] in env.files.state()
  decreases env
{
  var numArgs := env.constants.NumCommandLineArgs(env);
  if numArgs < 4 {
    print ""Not enough arguments, it requires 3"";
  }
  var compress := false;
  var uncompress := false;
  var bufferSize, writeBufferSize := 0, 0;
  var sucessLen := false;
  var original := env.constants.GetCommandLineArg(2, env);
  var copy := env.constants.GetCommandLineArg(3, env);
  var arg := env.constants.GetCommandLineArg(1, env);
  uncompress := arg[..] == ""1""[..];
  compress := arg[..] == ""0""[..];
  assert compress ==> env.constants.CommandLineArgs()[1] == ""0""[..];
  assert uncompress ==> env.constants.CommandLineArgs()[1] == ""1""[..];
  var OriginalExist := FileStream.FileExists(original, env);
  if !OriginalExist {
    print ""Original file not found..."";
  }
  assert OriginalExist ==> old(env.constants.CommandLineArgs())[2] in env.files.state();
  var CopyExist := FileStream.FileExists(copy, env);
  assert CopyExist ==> old(env.constants.CommandLineArgs())[3] in env.files.state();
  if CopyExist {
    print ""Destination file already exists"";
  }
  if OriginalExist && !CopyExist && (uncompress || compress) {
    sucessLen, bufferSize := FileStream.FileLength(original, env);
  }
  var originalStream, copyStream;
  var successOriginal, successCopy := false, false;
  var successRead, successWrite := false, false;
  var successClose, successCloseCopy := false, false;
  if sucessLen && !CopyExist {
    var buffer := new byte[bufferSize];
    successOriginal, originalStream := FileStream.Open(original, env);
    if successOriginal {
      successCopy, copyStream := FileStream.Open(copy, env);
      if successCopy {
        successRead := originalStream.Read(0, buffer, 0, bufferSize);
        assert env.ok.ok() ==> old(env.files.state())[original[..]] == buffer[..];
        if successRead {
          var buffer2;
          if compress {
            buffer2 := compress_impl(buffer);
          } else {
            buffer2 := decompress_impl(buffer);
          }
          successWrite := copyStream.Write(0, buffer2, 0, |buffer2[..]|);
          if successWrite {
            successClose := originalStream.Close();
            if successClose {
              successCloseCopy := copyStream.Close();
              if successCloseCopy {
                print ""DONE!"";
              }
            }
          }
        }
      }
    }
  }
  if !successCloseCopy && OriginalExist && !CopyExist {
    print ""Something went wrong"";
  }
}

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
  decreases s
{
  a := new A[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
}

function method padding(counter: int, a: seq<byte>): seq<byte>
  decreases counter
{
  padd(counter) + a
}

function method padd(counter: int): seq<byte>
  decreases counter
{
  if counter <= 0 then
    []
  else
    [0] + padd(counter - 1)
}

function check4codelen(bytes: seq<byte>): int
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  decreases bytes
{
  check4codelenHelper(bytes, 1)
}

function check4codelenHelper(bytes: seq<byte>, counter: int): int
  requires exists i: int :: 1 <= i < |bytes| && bytes[0] == bytes[i] && forall j: int :: 0 < j < i ==> bytes[j] == 0
  requires 1 <= counter < |bytes|
  decreases |bytes| - counter
{
  if counter >= |bytes| - 1 then
    -1
  else if bytes[0] == bytes[counter] then
    counter
  else
    check4codelenHelper(bytes, counter + 1)
}

function padder(bytes: seq<seq<byte>>, limit: int, codelen: int): seq<byte>
  requires 0 <= limit <= |bytes|
  decreases bytes, limit, codelen
{
  padderRecursion(bytes, limit, codelen, 0)
}

function padderRecursion(bytes: seq<seq<byte>>, limit: int, codelen: int, counter: int): seq<byte>
  requires 0 <= limit <= |bytes|
  requires 0 <= counter <= limit
  decreases limit - counter
{
  if limit == counter then
    []
  else
    padding(codelen - |bytes[counter]|, bytes[counter]) + padderRecursion(bytes, limit, codelen, counter + 1)
}

newtype {:nativeType ""byte""} byte = b: int
  | 0 <= b < 256

newtype {:nativeType ""ushort""} uint16 = i: int
  | 0 <= i < 65536

newtype {:nativeType ""int""} int32 = i: int
  | -2147483648 <= i < 2147483648

newtype {:nativeType ""uint""} uint32 = i: int
  | 0 <= i < 4294967296

newtype {:nativeType ""ulong""} uint64 = i: int
  | 0 <= i < 18446744073709551616

newtype {:nativeType ""int""} nat32 = i: int
  | 0 <= i < 2147483648

class HostEnvironment {
  ghost var constants: HostConstants?
  ghost var ok: OkState?
  ghost var files: FileSystemState?

  constructor {:axiom} ()

  predicate Valid()
    reads this
    decreases {this}
  {
    constants != null &&
    ok != null &&
    files != null
  }

  method {:axiom} foo()
    ensures Valid()
}

class HostConstants {
  constructor {:axiom} ()
    requires false

  function {:axiom} CommandLineArgs(): seq<seq<char>>
    reads this
    decreases {this}

  static method {:extern} NumCommandLineArgs(ghost env: HostEnvironment) returns (n: uint32)
    requires env.Valid()
    ensures n as int == |env.constants.CommandLineArgs()|
    decreases env

  static method {:extern} GetCommandLineArg(i: uint64, ghost env: HostEnvironment) returns (arg: array<char>)
    requires env.Valid()
    requires 0 <= i as int < |env.constants.CommandLineArgs()|
    ensures fresh(arg)
    ensures arg[..] == env.constants.CommandLineArgs()[i]
    decreases i, env
}

class OkState {
  constructor {:axiom} ()
    requires false

  function {:axiom} ok(): bool
    reads this
    decreases {this}
}

class FileSystemState {
  constructor {:axiom} ()
    requires false

  function {:axiom} state(): map<seq<char>, seq<byte>>
    reads this
    decreases {this}
}

class FileStream {
  ghost var env: HostEnvironment

  function {:axiom} Name(): seq<char>
    reads this
    decreases {this}

  function {:axiom} IsOpen(): bool
    reads this
    decreases {this}

  constructor {:axiom} ()
    requires false

  static method {:extern} FileExists(name: array<char>, ghost env: HostEnvironment?) returns (result: bool)
    requires env != null && env.Valid()
    requires env.ok.ok()
    ensures result <==> old(name[..]) in env.files.state()
    decreases name, env

  static method {:extern} FileLength(name: array<char>, ghost env: HostEnvironment)
      returns (success: bool, len: int32)
    requires env.Valid()
    requires env.ok.ok()
    requires name[..] in env.files.state()
    modifies env.ok
    ensures env.ok.ok() == success
    ensures success ==> len as int == |env.files.state()[name[..]]|
    decreases name, env

  static method {:extern} Open(name: array<char>, ghost env: HostEnvironment)
      returns (ok: bool, f: FileStream)
    requires env.Valid()
    requires env.ok.ok()
    modifies env.ok, env.files
    ensures env.ok.ok() == ok
    ensures ok ==> fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..] && env.files.state() == if name[..] in old(env.files.state()) then old(env.files.state()) else old(env.files.state())[name[..] := []]
    decreases name, env

  method {:extern} Close() returns (ok: bool)
    requires env.Valid()
    requires env.ok.ok()
    requires IsOpen()
    modifies this, env.ok
    ensures env == old(env)
    ensures env.ok.ok() == ok
    ensures !IsOpen()

  method {:extern} Read(file_offset: nat32, buffer: array?<byte>, start: int32, num_bytes: int32)
      returns (ok: bool)
    requires env.Valid()
    requires env.ok.ok()
    requires IsOpen()
    requires buffer != null
    requires Name() in env.files.state()
    requires file_offset as int + num_bytes as int <= |env.files.state()[Name()]|
    requires 0 <= start as int <= start as int + num_bytes as int <= buffer.Length
    modifies this, env.ok, env.files, buffer
    ensures env == old(env)
    ensures env.ok.ok() == ok
    ensures ok ==> env.files.state() == old(env.files.state())
    ensures Name() == old(Name())
    ensures ok ==> IsOpen()
    ensures ok ==> buffer[..] == buffer[..start] + env.files.state()[Name()][file_offset .. file_offset as int + num_bytes as int] + buffer[start as int + num_bytes as int..]
    decreases file_offset, buffer, start, num_bytes

  method {:extern} Write(file_offset: nat32, buffer: array?<byte>, start: int32, num_bytes: int)
      returns (ok: bool)
    requires env.Valid()
    requires env.ok.ok()
    requires IsOpen()
    requires buffer != null
    requires Name() in env.files.state()
    requires file_offset as int <= |env.files.state()[Name()]|
    requires 0 <= start as int <= start as int + num_bytes as int <= buffer.Length
    modifies this, env.ok, env.files
    ensures num_bytes < 2147483648 ==> ok == false
    ensures env == old(env)
    ensures env.ok.ok() == ok
    ensures Name() == old(Name())
    ensures ok ==> IsOpen()
    ensures ok ==> var old_file: seq<byte> := old(env.files.state()[Name()]); env.files.state() == old(env.files.state())[Name() := old_file[..file_offset] + buffer[start .. start as int + num_bytes as int]]
    decreases file_offset, buffer, start, num_bytes
}
")]

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public int Length {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongLength {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Length {
      get { return this.setImpl.Count; }
    }
    public long LongLength {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Length < other.Length && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, int> dict;
#else
    readonly Dictionary<T, int> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, int>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, int> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, int>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = 1;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (int i = 0; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> ElementsWithoutDuplicates {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Count);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Length {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongLength {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !Dafny.Helpers.AreEqual(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!Dafny.Helpers.AreEqual(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
    public Set<U> Keys
    {
      get
      {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values
    {
      get
      {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<@_System.@__tuple_h2<U, V>> Items
    {
      get
      {
        HashSet<@_System.@__tuple_h2<U, V>> result = new HashSet<@_System.@__tuple_h2<U, V>>();
        if (hasNullValue) {
          result.Add(new @_System.@__tuple_h2<U, V>(new @_System.@__tuple_h2____hMake2<U, V>(default(U), nullValue)));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(new @_System.@__tuple_h2<U,V>(new @_System.@__tuple_h2____hMake2<U, V>(kvp.Key, kvp.Value)));
        }
        return Dafny.Set<@_System.@__tuple_h2<U, V>>.FromCollection(result);
      }
    }
  }

  public class Sequence<T>
  {
    readonly T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Length {
      get { return elmts.Length; }
    }
    public long LongLength {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!Dafny.Helpers.AreEqual(elmts[i], other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (Dafny.Helpers.AreEqual(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static bool AreEqual<G>(G a, G b) {
      return a == null ? b == null : a.Equals(b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }
    public static string ToString<G>(G g) {
      return g == null ? "null" : g.ToString();
    }
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    public static System.Predicate<BigInteger> PredicateConverter_byte(System.Predicate<byte> pred) {
      return x => pred((byte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_sbyte(System.Predicate<sbyte> pred) {
      return x => pred((sbyte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ushort(System.Predicate<ushort> pred) {
      return x => pred((ushort)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_short(System.Predicate<short> pred) {
      return x => pred((short)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_uint(System.Predicate<uint> pred) {
      return x => pred((uint)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_int(System.Predicate<int> pred) {
      return x => pred((int)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ulong(System.Predicate<ulong> pred) {
      return x => pred((ulong)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_long(System.Predicate<long> pred) {
      return x => pred((long)x);
    }
    // Computing forall/exists quantifiers
    public static bool QuantBool(bool frall, System.Predicate<bool> pred) {
      if (frall) {
        return pred(false) && pred(true);
      } else {
        return pred(false) || pred(true);
      }
    }
    public static bool QuantChar(bool frall, System.Predicate<char> pred) {
      for (int i = 0; i < 0x10000; i++) {
        if (pred((char)i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantInt(BigInteger lo, BigInteger hi, bool frall, System.Predicate<BigInteger> pred) {
      for (BigInteger i = lo; i < hi; i++) {
        if (pred(i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSingle<U>(U u, bool frall, System.Predicate<U> pred) {
      return pred(u);
    }
    public static bool QuantSet<U>(Dafny.Set<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMultiSet<U>(Dafny.MultiSet<U> multiset, bool frall, System.Predicate<U> pred) {
      foreach (var u in multiset.ElementsWithoutDuplicates) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSubSets<U>(Dafny.Set<U> set, bool frall, System.Predicate<Dafny.Set<U>> pred) {
      foreach (var u in set.AllSubsets) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMap<U,V>(Dafny.Map<U,V> map, bool frall, System.Predicate<U> pred) {
      foreach (var u in map.Domain) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSeq<U>(Dafny.Sequence<U> seq, bool frall, System.Predicate<U> pred) {
      foreach (var u in seq.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantDatatype<U>(IEnumerable<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public delegate Dafny.Set<T> ComprehensionDelegate<T>();
    public delegate Dafny.Map<U, V> MapComprehensionDelegate<U, V>();
    public static IEnumerable<bool> AllBooleans {
      get {
        yield return false;
        yield return true;
      }
    }
    public static IEnumerable<char> AllChars {
      get {
        for (int i = 0; i < 0x10000; i++) {
          yield return (char)i;
        }
      }
    }
    public static IEnumerable<BigInteger> AllIntegers {
      get {
        yield return new BigInteger(0);
        for (var j = new BigInteger(1);; j++) {
          yield return j;
          yield return -j;
        }
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public delegate Result Function<Input,Result>(Input input);

    public static A Id<A>(A a) {
      return a;
    }

    public static bool BigOrdinal_IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool BigOrdinal_IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger BigOrdinal_Offset(BigInteger ord) {
      return ord;
    }
    public static bool BigOrdinal_IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}

namespace @_System
{

  public abstract class Base___tuple_h2<@T0, @T1> { }
  public class __tuple_h2____hMake2<@T0, @T1> : Base___tuple_h2<@T0, @T1>
  {
    public readonly @T0 @_0;
    public readonly @T1 @_1;
    public __tuple_h2____hMake2(@T0 @_0, @T1 @_1)
    {
      this.@_0 = @_0;
      this.@_1 = @_1;
    }
    public override bool Equals(object other)
    {
      var oth = other as _System.@__tuple_h2____hMake2<@T0, @T1>;
      return oth != null && this.@_0.Equals(oth.@_0) && Dafny.Helpers.AreEqual(this.@_1, oth.@_1);
    }
    public override int GetHashCode()
    {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@_0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@_1));
      return (int)hash;
    }
    public override string ToString()
    {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.@_0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.@_1);
      s += ")";
      return s;
    }
  }
  public struct @__tuple_h2<@T0, @T1>
  {
    Base___tuple_h2<@T0, @T1> _d;
    public Base___tuple_h2<@T0, @T1> _D
    {
      get
      {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h2(Base___tuple_h2<@T0, @T1> d) { this._d = d; }
    static Base___tuple_h2<@T0, @T1> theDefault;
    public static Base___tuple_h2<@T0, @T1> Default
    {
      get
      {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h2____hMake2<@T0, @T1>(default(@T0), default(@T1));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other)
    {
      return other is @__tuple_h2<@T0, @T1> && _D.Equals(((@__tuple_h2<@T0, @T1>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake2 { get { return _D is __tuple_h2____hMake2<@T0, @T1>; } }
    public @T0 dtor__0 { get { return ((__tuple_h2____hMake2<@T0, @T1>)_D).@_0; } }
    public @T1 dtor__1 { get { return ((__tuple_h2____hMake2<@T0, @T1>)_D).@_1; } }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
      public static T[] InitNewArray1<T>(T z, BigInteger size0) {
        int s0 = (int)size0;
        T[] a = new T[s0];
        for (int i0 = 0; i0 < s0; i0++)
          a[i0] = z;
        return a;
      }
  }
}
namespace @_System {



  public abstract class Base___tuple_h0 { }
  public class __tuple_h0____hMake0 : Base___tuple_h0 {
    public __tuple_h0____hMake0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.@__tuple_h0____hMake0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      return s;
    }
  }
  public struct @__tuple_h0 {
    Base___tuple_h0 _d;
    public Base___tuple_h0 _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h0(Base___tuple_h0 d) { this._d = d; }
    static Base___tuple_h0 theDefault;
    public static Base___tuple_h0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h0____hMake0();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @__tuple_h0 && _D.Equals(((@__tuple_h0)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake0 { get { return _D is __tuple_h0____hMake0; } }
    public static System.Collections.Generic.IEnumerable<@__tuple_h0> AllSingletonConstructors {
      get {
        yield return new @__tuple_h0(new __tuple_h0____hMake0());
        yield break;
      }
    }
  }
} // end of namespace _System
namespace @__default {

  public partial class @__default {
    public static void @compress__impl(byte[] @bytes, out byte[] @compressed__bytes)
    {
      @compressed__bytes = (byte[])null;
      if ((new BigInteger((@bytes).@Length)) <= (new BigInteger(1)))
      {
        byte[] _rhs0 = @bytes;
        @compressed__bytes = _rhs0;
        byte[] _rhs1 = @compressed__bytes;
        @compressed__bytes = _rhs1;
        return;
      }
      BigInteger @_627_dictSize = BigInteger.Zero;
      BigInteger _rhs2 = new BigInteger(0);
      @_627_dictSize = _rhs2;
      BigInteger @_628_codelen = BigInteger.Zero;
      BigInteger _rhs3 = new BigInteger(1);
      @_628_codelen = _rhs3;
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> @_629_dict = Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.Empty;
      byte @_630_i = 0;
      byte _rhs4 = 0;
      @_630_i = _rhs4;
      while ((@_630_i) < (255))
      {
        Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs5 = (@_629_dict).Update(Dafny.Sequence<byte>.FromElements(@_630_i), Dafny.Sequence<byte>.FromElements(@_630_i));
        @_629_dict = _rhs5;
        { }
        BigInteger _rhs6 = (@_627_dictSize) + (new BigInteger(1));
        @_627_dictSize = _rhs6;
        byte _rhs7 = (byte)((@_630_i) + (1));
        @_630_i = _rhs7;
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Create base dictionary\n"));
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs8 = (@_629_dict).Update(Dafny.Sequence<byte>.FromElements(@_630_i), Dafny.Sequence<byte>.FromElements(@_630_i));
      @_629_dict = _rhs8;
      BigInteger _rhs9 = (@_627_dictSize) + (new BigInteger(1));
      @_627_dictSize = _rhs9;
      { }
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> @_631_dictb = Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.Empty;
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs10 = @_629_dict;
      @_631_dictb = _rhs10;
      BigInteger @_632_currentByte = BigInteger.Zero;
      BigInteger _rhs11 = new BigInteger(0);
      @_632_currentByte = _rhs11;
      Dafny.Sequence<byte> @_633_windowchain = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs12 = Dafny.Sequence<byte>.FromElements();
      @_633_windowchain = _rhs12;
      Dafny.Sequence<byte> @_634_w = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs13 = Dafny.Sequence<byte>.FromElements();
      @_634_w = _rhs13;
      Dafny.Sequence<Dafny.Sequence<byte>> @_635_out = Dafny.Sequence<Dafny.Sequence<byte>>.Empty;
      Dafny.Sequence<Dafny.Sequence<byte>> _rhs14 = Dafny.Sequence<Dafny.Sequence<byte>>.FromElements();
      @_635_out = _rhs14;
      { }
      BigInteger @_636_percentageHelper = BigInteger.Zero;
      BigInteger _rhs15 = Dafny.Helpers.EuclideanDivision(new BigInteger((@bytes).@Length), new BigInteger(10));
      @_636_percentageHelper = _rhs15;
      System.Console.Write(Dafny.Sequence<char>.FromString("0% "));
      while ((@_632_currentByte) < (new BigInteger((Dafny.Helpers.SeqFromArray(@bytes)).Length)))
      {
        { }
        Dafny.Sequence<byte> _rhs16 = (@_634_w).@Concat(Dafny.Sequence<byte>.FromElements((@bytes)[(int)(@_632_currentByte)]));
        @_633_windowchain = _rhs16;
        if ((@_629_dict).@Contains(@_633_windowchain))
        {
          Dafny.Sequence<byte> _rhs17 = Dafny.Sequence<byte>.FromElements();
          @_634_w = _rhs17;
          Dafny.Sequence<byte> _rhs18 = @_633_windowchain;
          @_634_w = _rhs18;
          { }
        }
        else
        {
          if ((@_629_dict).@Contains(@_634_w))
          {
            { }
            Dafny.Sequence<Dafny.Sequence<byte>> _rhs19 = (@_635_out).@Concat(Dafny.Sequence<Dafny.Sequence<byte>>.FromElements((@_629_dict).Select(@_634_w)));
            @_635_out = _rhs19;
            { }
          }
          BigInteger @_637_auxDict = BigInteger.Zero;
          BigInteger _rhs20 = @_627_dictSize;
          @_637_auxDict = _rhs20;
          Dafny.Sequence<byte> @_638_aux = Dafny.Sequence<byte>.Empty;
          Dafny.Sequence<byte> _rhs21 = Dafny.Sequence<byte>.FromElements();
          @_638_aux = _rhs21;
          { }
          while ((@_637_auxDict) >= (new BigInteger(256)))
          {
            Dafny.Sequence<byte> _rhs22 = (Dafny.Sequence<byte>.FromElements((byte)(Dafny.Helpers.EuclideanModulus(@_637_auxDict, new BigInteger(256))))).@Concat(@_638_aux);
            @_638_aux = _rhs22;
            BigInteger _rhs23 = Dafny.Helpers.EuclideanDivision(@_637_auxDict, new BigInteger(256));
            @_637_auxDict = _rhs23;
            { }
          }
          Dafny.Sequence<byte> _rhs24 = (Dafny.Sequence<byte>.FromElements((byte)(@_637_auxDict))).@Concat(@_638_aux);
          @_638_aux = _rhs24;
          Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs25 = (@_629_dict).Update(@_633_windowchain, @_638_aux);
          @_629_dict = _rhs25;
          BigInteger _rhs26 = (@_627_dictSize) + (new BigInteger(1));
          @_627_dictSize = _rhs26;
          Dafny.Sequence<byte> _rhs27 = Dafny.Sequence<byte>.FromElements((@bytes)[(int)(@_632_currentByte)]);
          @_634_w = _rhs27;
          { }
        }
        BigInteger _rhs28 = (@_632_currentByte) + (new BigInteger(1));
        @_632_currentByte = _rhs28;
        if (((new BigInteger((@bytes).@Length)) >= (new BigInteger(10))) && ((Dafny.Helpers.EuclideanModulus(@_632_currentByte, @_636_percentageHelper)) == (new BigInteger(0))))
        {
          System.Console.Write(Dafny.Sequence<char>.FromString("=> "));
          System.Console.Write(Dafny.Helpers.EuclideanDivision((new BigInteger(10)) * (@_632_currentByte), @_636_percentageHelper));
          System.Console.Write(Dafny.Sequence<char>.FromString("% "));
        }
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Finishing encoding cycle\n"));
      { }
      if ((new BigInteger((@_634_w).Length)) != (new BigInteger(0)))
      {
        Dafny.Sequence<Dafny.Sequence<byte>> _rhs29 = (@_635_out).@Concat(Dafny.Sequence<Dafny.Sequence<byte>>.FromElements((@_629_dict).Select(@_634_w)));
        @_635_out = _rhs29;
      }
      BigInteger @_639_cal = BigInteger.Zero;
      BigInteger _rhs30 = @_627_dictSize;
      @_639_cal = _rhs30;
      BigInteger @_640_countHelper = BigInteger.Zero;
      BigInteger _rhs31 = new BigInteger(1);
      @_640_countHelper = _rhs31;
      while ((@_639_cal) >= (new BigInteger(256)))
      {
        BigInteger _rhs32 = Dafny.Helpers.EuclideanDivision(@_639_cal, new BigInteger(256));
        @_639_cal = _rhs32;
        BigInteger _rhs33 = (@_640_countHelper) + (new BigInteger(1));
        @_640_countHelper = _rhs33;
      }
      BigInteger @_641_j = BigInteger.Zero;
      BigInteger _rhs34 = new BigInteger(0);
      @_641_j = _rhs34;
      Dafny.Sequence<byte> @_642_encoded = Dafny.Sequence<byte>.Empty;
      if ((new BigInteger((Dafny.Helpers.SeqFromArray(@bytes)).Length)) > (new BigInteger(0)))
      {
        Dafny.Sequence<byte> _rhs35 = Dafny.Sequence<byte>.FromElements((@bytes)[(int)(new BigInteger(0))]);
        @_642_encoded = _rhs35;
      }
      { }
      BigInteger _rhs36 = @_640_countHelper;
      @_628_codelen = _rhs36;
      { }
      Dafny.Sequence<byte> @_643_auxencoded = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs37 = Dafny.Sequence<byte>.FromElements();
      @_643_auxencoded = _rhs37;
      while ((@_641_j) < (new BigInteger((@_635_out).Length)))
      {
        Dafny.Sequence<byte> _rhs38 = Dafny.Sequence<byte>.FromElements();
        @_643_auxencoded = _rhs38;
        BigInteger _rhs39 = @_628_codelen;
        @_640_countHelper = _rhs39;
        { }
        if ((new BigInteger(((@_635_out).Select(@_641_j)).Length)) < (@_640_countHelper))
        {
          while ((new BigInteger(((@_635_out).Select(@_641_j)).Length)) < (@_640_countHelper))
          {
            Dafny.Sequence<byte> _rhs40 = (@_643_auxencoded).@Concat(Dafny.Sequence<byte>.FromElements(0));
            @_643_auxencoded = _rhs40;
            BigInteger _rhs41 = (@_640_countHelper) - (new BigInteger(1));
            @_640_countHelper = _rhs41;
            { }
          }
        }
        Dafny.Sequence<byte> _rhs42 = (@_643_auxencoded).@Concat((@_635_out).Select(@_641_j));
        @_643_auxencoded = _rhs42;
        Dafny.Sequence<byte> _rhs43 = (@_642_encoded).@Concat(@_643_auxencoded);
        @_642_encoded = _rhs43;
        { }
        BigInteger _rhs44 = (@_641_j) + (new BigInteger(1));
        @_641_j = _rhs44;
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Finish Padding\n"));
      { }
      byte[] _out0;
      @__default.@ArrayFromSeq<byte>(@_642_encoded, out _out0);
      @compressed__bytes = _out0;
      { }
      { }
    }
    public static void @decompress__impl(byte[] @compressed__bytes, out byte[] @bytes)
    {
      @bytes = (byte[])null;
      if ((new BigInteger((@compressed__bytes).@Length)) <= (new BigInteger(1)))
      {
        byte[] _rhs45 = @compressed__bytes;
        @bytes = _rhs45;
        byte[] _rhs46 = @bytes;
        @bytes = _rhs46;
        return;
      }
      BigInteger @_644_codelen = BigInteger.Zero;
      BigInteger _rhs47 = new BigInteger(1);
      @_644_codelen = _rhs47;
      { }
      byte @_645_firstByte = 0;
      byte _rhs48 = (@compressed__bytes)[(int)(new BigInteger(0))];
      @_645_firstByte = _rhs48;
      while ((@_645_firstByte) != ((@compressed__bytes)[(int)(@_644_codelen)]))
      {
        BigInteger _rhs49 = (@_644_codelen) + (new BigInteger(1));
        @_644_codelen = _rhs49;
        if ((@_644_codelen) == (new BigInteger((@compressed__bytes).@Length)))
        {
          System.Console.Write(Dafny.Sequence<char>.FromString("Something went wrong\n"));
          byte[] _rhs50 = @compressed__bytes;
          @bytes = _rhs50;
          byte[] _rhs51 = @bytes;
          @bytes = _rhs51;
          return;
        }
      }
      BigInteger @_646_dictSize = BigInteger.Zero;
      BigInteger _rhs52 = new BigInteger(0);
      @_646_dictSize = _rhs52;
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> @_647_dict = Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.Empty;
      byte @_648_i = 0;
      byte _rhs53 = 0;
      @_648_i = _rhs53;
      while ((@_648_i) < (255))
      {
        Dafny.Sequence<byte> @_649_auxbyte = Dafny.Sequence<byte>.Empty;
        Dafny.Sequence<byte> _rhs54 = @__default.@padding((@_644_codelen) - (new BigInteger(1)), Dafny.Sequence<byte>.FromElements(@_648_i));
        @_649_auxbyte = _rhs54;
        Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs55 = (@_647_dict).Update(@_649_auxbyte, Dafny.Sequence<byte>.FromElements(@_648_i));
        @_647_dict = _rhs55;
        { }
        { }
        BigInteger _rhs56 = (@_646_dictSize) + (new BigInteger(1));
        @_646_dictSize = _rhs56;
        byte _rhs57 = (byte)((@_648_i) + (1));
        @_648_i = _rhs57;
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Create base dictionary\n"));
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs58 = (@_647_dict).Update(@__default.@padding((@_644_codelen) - (new BigInteger(1)), Dafny.Sequence<byte>.FromElements(@_648_i)), Dafny.Sequence<byte>.FromElements(@_648_i));
      @_647_dict = _rhs58;
      BigInteger _rhs59 = (@_646_dictSize) + (new BigInteger(1));
      @_646_dictSize = _rhs59;
      { }
      BigInteger @_650_currentword = BigInteger.Zero;
      BigInteger _rhs60 = new BigInteger(1);
      @_650_currentword = _rhs60;
      System.Console.Write((@compressed__bytes)[(int)(new BigInteger(0))]);
      System.Console.Write(Dafny.Helpers.SeqFromArray(@compressed__bytes).Take((@_644_codelen) + (new BigInteger(1))).Drop(new BigInteger(1)));
      if (!(@_647_dict).@Contains(Dafny.Helpers.SeqFromArray(@compressed__bytes).Take((@_644_codelen) + (new BigInteger(1))).Drop(new BigInteger(1))))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Something went wrong!\n"));
        byte[] _rhs61 = @compressed__bytes;
        @bytes = _rhs61;
        byte[] _rhs62 = @bytes;
        @bytes = _rhs62;
        return;
      }
      Dafny.Sequence<byte> @_651_w = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs63 = (@_647_dict).Select(Dafny.Helpers.SeqFromArray(@compressed__bytes).Take((@_644_codelen) + (new BigInteger(1))).Drop(new BigInteger(1)));
      @_651_w = _rhs63;
      Dafny.Sequence<byte> @_652_out = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs64 = @_651_w;
      @_652_out = _rhs64;
      while ((((@_644_codelen) * ((@_650_currentword) + (new BigInteger(1)))) + (new BigInteger(1))) <= (new BigInteger((@compressed__bytes).@Length)))
      {
        Dafny.Sequence<byte> @_653_windowchain = Dafny.Sequence<byte>.Empty;
        Dafny.Sequence<byte> _rhs65 = Dafny.Helpers.SeqFromArray(@compressed__bytes).Take(((@_644_codelen) * ((@_650_currentword) + (new BigInteger(1)))) + (new BigInteger(1))).Drop(((@_644_codelen) * (@_650_currentword)) + (new BigInteger(1)));
        @_653_windowchain = _rhs65;
        Dafny.Sequence<byte> @_654_entry = Dafny.Sequence<byte>.Empty;
        if ((@_647_dict).@Contains(@_653_windowchain))
        {
          Dafny.Sequence<byte> _rhs66 = (@_647_dict).Select(@_653_windowchain);
          @_654_entry = _rhs66;
        }
        else
        {
          BigInteger @_655_auxDict = BigInteger.Zero;
          BigInteger _rhs67 = @_646_dictSize;
          @_655_auxDict = _rhs67;
          Dafny.Sequence<byte> @_656_aux = Dafny.Sequence<byte>.Empty;
          Dafny.Sequence<byte> _rhs68 = Dafny.Sequence<byte>.FromElements();
          @_656_aux = _rhs68;
          { }
          while ((@_655_auxDict) >= (new BigInteger(256)))
          {
            Dafny.Sequence<byte> _rhs69 = (Dafny.Sequence<byte>.FromElements((byte)(Dafny.Helpers.EuclideanModulus(@_655_auxDict, new BigInteger(256))))).@Concat(@_656_aux);
            @_656_aux = _rhs69;
            BigInteger _rhs70 = Dafny.Helpers.EuclideanDivision(@_655_auxDict, new BigInteger(256));
            @_655_auxDict = _rhs70;
            { }
          }
          Dafny.Sequence<byte> _rhs71 = (Dafny.Sequence<byte>.FromElements((byte)(Dafny.Helpers.EuclideanModulus(@_655_auxDict, new BigInteger(256))))).@Concat(@_656_aux);
          @_656_aux = _rhs71;
          if (((@_656_aux).@Equals(@_653_windowchain)) && ((new BigInteger((@_651_w).Length)) > (new BigInteger(0))))
          {
            Dafny.Sequence<byte> _rhs72 = (@_651_w).@Concat(Dafny.Sequence<byte>.FromElements((@_651_w).Select(new BigInteger(0))));
            @_654_entry = _rhs72;
            System.Console.Write(@_654_entry);
          }
        }
        if ((new BigInteger((@_654_entry).Length)) > (new BigInteger(0)))
        {
          Dafny.Sequence<byte> _rhs73 = (@_652_out).@Concat(@_654_entry);
          @_652_out = _rhs73;
          BigInteger @_657_auxDict = BigInteger.Zero;
          BigInteger _rhs74 = @_646_dictSize;
          @_657_auxDict = _rhs74;
          Dafny.Sequence<byte> @_658_aux = Dafny.Sequence<byte>.Empty;
          Dafny.Sequence<byte> _rhs75 = Dafny.Sequence<byte>.FromElements();
          @_658_aux = _rhs75;
          { }
          while ((@_657_auxDict) >= (new BigInteger(256)))
          {
            Dafny.Sequence<byte> _rhs76 = (Dafny.Sequence<byte>.FromElements((byte)(Dafny.Helpers.EuclideanModulus(@_657_auxDict, new BigInteger(256))))).@Concat(@_658_aux);
            @_658_aux = _rhs76;
            BigInteger _rhs77 = Dafny.Helpers.EuclideanDivision(@_657_auxDict, new BigInteger(256));
            @_657_auxDict = _rhs77;
            { }
          }
          Dafny.Sequence<byte> _rhs78 = (Dafny.Sequence<byte>.FromElements((byte)(@_657_auxDict))).@Concat(@_658_aux);
          @_658_aux = _rhs78;
          Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs79 = (@_647_dict).Update(@__default.@padding((@_644_codelen) - (new BigInteger((@_658_aux).Length)), @_658_aux), (@_651_w).@Concat(Dafny.Sequence<byte>.FromElements((@_654_entry).Select(new BigInteger(0)))));
          @_647_dict = _rhs79;
          BigInteger _rhs80 = (@_646_dictSize) + (new BigInteger(1));
          @_646_dictSize = _rhs80;
          Dafny.Sequence<byte> _rhs81 = @_654_entry;
          @_651_w = _rhs81;
        }
        BigInteger _rhs82 = (@_650_currentword) + (new BigInteger(1));
        @_650_currentword = _rhs82;
      }
      byte[] _out1;
      @__default.@ArrayFromSeq<byte>(@_652_out, out _out1);
      @bytes = _out1;
    }
    public static void @Main()
    {
    TAIL_CALL_START: ;
      uint @_659_numArgs = 0;
      uint _out2;
      @HostConstants.@NumCommandLineArgs(out _out2);
      @_659_numArgs = _out2;
      if ((@_659_numArgs) < (4U))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Not enough arguments, it requires 3"));
      }
      bool @_660_compress = false;
      bool _rhs83 = false;
      @_660_compress = _rhs83;
      bool @_661_uncompress = false;
      bool _rhs84 = false;
      @_661_uncompress = _rhs84;
      int @_662_bufferSize = 0;
      BigInteger @_663_writeBufferSize = BigInteger.Zero;
      int _rhs86 = 0;
      int _rhs85 = _rhs86;
      BigInteger _rhs88 = new BigInteger(0);
      BigInteger _rhs87 = _rhs88;
      @_662_bufferSize = _rhs85;
      @_663_writeBufferSize = _rhs87;
      bool @_664_sucessLen = false;
      bool _rhs89 = false;
      @_664_sucessLen = _rhs89;
      char[] @_665_original = (char[])null;
      char[] _out3;
      @HostConstants.@GetCommandLineArg(2UL, out _out3);
      @_665_original = _out3;
      char[] @_666_copy = new char[0];
      char[] _out4;
      @HostConstants.@GetCommandLineArg(3UL, out _out4);
      @_666_copy = _out4;
      char[] @_667_arg = (char[])null;
      char[] _out5;
      @HostConstants.@GetCommandLineArg(1UL, out _out5);
      @_667_arg = _out5;
      bool _rhs90 = (Dafny.Helpers.SeqFromArray(@_667_arg)).@Equals((Dafny.Sequence<char>.FromString("1")));
      @_661_uncompress = _rhs90;
      bool _rhs91 = (Dafny.Helpers.SeqFromArray(@_667_arg)).@Equals((Dafny.Sequence<char>.FromString("0")));
      @_660_compress = _rhs91;
      { }
      { }
      bool @_668_OriginalExist = false;
      bool _out6;
      @FileStream.@FileExists(@_665_original, out _out6);
      @_668_OriginalExist = _out6;
      if (!(@_668_OriginalExist))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Original file not found..."));
      }
      { }
      bool @_669_CopyExist = false;
      bool _out7;
      @FileStream.@FileExists(@_666_copy, out _out7);
      @_669_CopyExist = _out7;
      { }
      if (@_669_CopyExist)
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Destination file already exists"));
      }
      if (((@_668_OriginalExist) && (!(@_669_CopyExist))) && ((@_661_uncompress) || (@_660_compress)))
      {
        bool _out8;
        int _out9;
        @FileStream.@FileLength(@_665_original, out _out8, out _out9);
        @_664_sucessLen = _out8;
        @_662_bufferSize = _out9;
      }
      @FileStream @_670_originalStream = default(@FileStream);
      @FileStream @_671_copyStream = default(@FileStream);
      bool @_672_successOriginal = false;
      bool @_673_successCopy = false;
      bool _rhs93 = false;
      bool _rhs92 = _rhs93;
      bool _rhs95 = false;
      bool _rhs94 = _rhs95;
      @_672_successOriginal = _rhs92;
      @_673_successCopy = _rhs94;
      bool @_674_successRead = false;
      bool @_675_successWrite = false;
      bool _rhs97 = false;
      bool _rhs96 = _rhs97;
      bool _rhs99 = false;
      bool _rhs98 = _rhs99;
      @_674_successRead = _rhs96;
      @_675_successWrite = _rhs98;
      bool @_676_successClose = false;
      bool @_677_successCloseCopy = false;
      bool _rhs101 = false;
      bool _rhs100 = _rhs101;
      bool _rhs103 = false;
      bool _rhs102 = _rhs103;
      @_676_successClose = _rhs100;
      @_677_successCloseCopy = _rhs102;
      if ((@_664_sucessLen) && (!(@_669_CopyExist)))
      {
        byte[] @_678_buffer = (byte[])null;
        var _nw0 = new byte[(int)(@_662_bufferSize)];
        @_678_buffer = _nw0;
        bool _out10;
        @FileStream _out11;
        @FileStream.@Open(@_665_original, out _out10, out _out11);
        @_672_successOriginal = _out10;
        @_670_originalStream = _out11;
        if (@_672_successOriginal)
        {
          bool _out12;
          @FileStream _out13;
          @FileStream.@Open(@_666_copy, out _out12, out _out13);
          @_673_successCopy = _out12;
          @_671_copyStream = _out13;
          if (@_673_successCopy)
          {
            bool _out14;
            (@_670_originalStream).@Read(0, @_678_buffer, 0, @_662_bufferSize, out _out14);
            @_674_successRead = _out14;
            { }
            if (@_674_successRead)
            {
              byte[] @_679_buffer2 = (byte[])null;
              if (@_660_compress)
              {
                byte[] _out15;
                @__default.@compress__impl(@_678_buffer, out _out15);
                @_679_buffer2 = _out15;
              }
              else
              {
                byte[] _out16;
                @__default.@decompress__impl(@_678_buffer, out _out16);
                @_679_buffer2 = _out16;
              }
              bool _out17;
              (@_671_copyStream).@Write(0, @_679_buffer2, 0, new BigInteger((Dafny.Helpers.SeqFromArray(@_679_buffer2)).Length), out _out17);
              @_675_successWrite = _out17;
              if (@_675_successWrite)
              {
                bool _out18;
                (@_670_originalStream).@Close(out _out18);
                @_676_successClose = _out18;
                if (@_676_successClose)
                {
                  bool _out19;
                  (@_671_copyStream).@Close(out _out19);
                  @_677_successCloseCopy = _out19;
                  if (@_677_successCloseCopy)
                  {
                    System.Console.Write(Dafny.Sequence<char>.FromString("DONE!"));
                  }
                }
              }
            }
          }
        }
      }
      if (((!(@_677_successCloseCopy)) && (@_668_OriginalExist)) && (!(@_669_CopyExist)))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Something went wrong"));
      }
    }
    public static void @ArrayFromSeq<@A>(Dafny.Sequence<@A> @s, out @A[] @a)
    {
      @a = new @A[0];
    TAIL_CALL_START: ;
      var _nw1 = new @A[(int)(new BigInteger((@s).Length))];
      var _arrayinit0 = Dafny.Helpers.Id<@Func<Dafny.Sequence<@A>,@Func<BigInteger,@A>>>((@_680_s) => (@_681_i) => (@_680_s).Select(@_681_i))(@s);
      for (int _arrayinit_00 = 0; _arrayinit_00 < _nw1.Length; _arrayinit_00++) {
        _nw1[_arrayinit_00] = _arrayinit0(_arrayinit_00);
      }
      @a = _nw1;
    }
    public static Dafny.Sequence<byte> @padding(BigInteger @counter, Dafny.Sequence<byte> @a) {
      return (@__default.@padd(@counter)).@Concat(@a);
    }
    public static Dafny.Sequence<byte> @padd(BigInteger @counter) {
      if ((@counter) <= (new BigInteger(0))) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        return (Dafny.Sequence<byte>.FromElements(0)).@Concat(@__default.@padd((@counter) - (new BigInteger(1))));
      }
    }
  }

  public class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
  }

  public class @uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
  }

  public class @int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public class @uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
  }

  public class @uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
  }

  public class @nat32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public partial class @HostEnvironment {
  }

  public partial class @HostConstants {
  }

  public partial class @OkState {
  }

  public partial class @FileSystemState {
  }

  public partial class @FileStream {
  }
} // end of namespace @__default
