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
  decreases bytes
{
  bytes
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
  print ""Create base dictionary"";
  dict := dict[[i] := [i]];
  assert forall b: byte :: [b] in dict;
  var dictb := dict;
  var currentByte := 0;
  var windowchain: seq<byte> := [];
  var w: seq<byte> := [];
  var out: seq<seq<byte>> := [];
  assert |out| == 0;
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
    print [currentByte];
    print ""\n"";
    currentByte := currentByte + 1;
  }
  print ""Finish encoding cycle"";
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
    codelen := countHelper;
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
  print ""Finish Padding"";
  assert |bytes[..]| > 0 ==> encoded[0] == bytes[0];
  compressed_bytes := ArrayFromSeq<byte>(encoded);
  assert |bytes[..]| > 0 ==> encoded[0] == compressed_bytes[0];
  assert |bytes[..]| > 0 ==> bytes[0] == compressed_bytes[0];
}

method decompress_impl(compressed_bytes: array?<byte>) returns (bytes: array?<byte>)
  requires compressed_bytes != null
  ensures bytes != null
  ensures bytes[..] == decompress(compressed_bytes[..])
  decreases compressed_bytes
{
  bytes := compressed_bytes;
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
  requires |env.constants.CommandLineArgs()| >= 4
  requires env.constants.CommandLineArgs()[1] == ""1""[..] || env.constants.CommandLineArgs()[1] == ""0""[..]
  requires env.constants.CommandLineArgs()[2] in env.files.state()
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

function padding(counter: int, a: seq<byte>): seq<byte>
  decreases counter
{
  a + padd(counter)
}

function padd(counter: int): seq<byte>
  decreases counter
{
  if counter <= 0 then
    []
  else
    [0] + padd(counter - 1)
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
      BigInteger @_296_dictSize = BigInteger.Zero;
      BigInteger _rhs0 = new BigInteger(0);
      @_296_dictSize = _rhs0;
      BigInteger @_297_codelen = BigInteger.Zero;
      BigInteger _rhs1 = new BigInteger(1);
      @_297_codelen = _rhs1;
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> @_298_dict = Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.Empty;
      byte @_299_i = 0;
      byte _rhs2 = 0;
      @_299_i = _rhs2;
      while ((@_299_i) < (255))
      {
        Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs3 = (@_298_dict).Update(Dafny.Sequence<byte>.FromElements(@_299_i), Dafny.Sequence<byte>.FromElements(@_299_i));
        @_298_dict = _rhs3;
        { }
        BigInteger _rhs4 = (@_296_dictSize) + (new BigInteger(1));
        @_296_dictSize = _rhs4;
        byte _rhs5 = (byte)((@_299_i) + (1));
        @_299_i = _rhs5;
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Create base dictionary"));
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs6 = (@_298_dict).Update(Dafny.Sequence<byte>.FromElements(@_299_i), Dafny.Sequence<byte>.FromElements(@_299_i));
      @_298_dict = _rhs6;
      { }
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> @_300_dictb = Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>>.Empty;
      Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs7 = @_298_dict;
      @_300_dictb = _rhs7;
      BigInteger @_301_currentByte = BigInteger.Zero;
      BigInteger _rhs8 = new BigInteger(0);
      @_301_currentByte = _rhs8;
      Dafny.Sequence<byte> @_302_windowchain = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs9 = Dafny.Sequence<byte>.FromElements();
      @_302_windowchain = _rhs9;
      Dafny.Sequence<byte> @_303_w = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs10 = Dafny.Sequence<byte>.FromElements();
      @_303_w = _rhs10;
      Dafny.Sequence<Dafny.Sequence<byte>> @_304_out = Dafny.Sequence<Dafny.Sequence<byte>>.Empty;
      Dafny.Sequence<Dafny.Sequence<byte>> _rhs11 = Dafny.Sequence<Dafny.Sequence<byte>>.FromElements();
      @_304_out = _rhs11;
      { }
      while ((@_301_currentByte) < (new BigInteger((Dafny.Helpers.SeqFromArray(@bytes)).Length)))
      {
        { }
        Dafny.Sequence<byte> _rhs12 = (@_303_w).@Concat(Dafny.Sequence<byte>.FromElements((@bytes)[(int)(@_301_currentByte)]));
        @_302_windowchain = _rhs12;
        if ((@_298_dict).@Contains(@_302_windowchain))
        {
          Dafny.Sequence<byte> _rhs13 = Dafny.Sequence<byte>.FromElements();
          @_303_w = _rhs13;
          Dafny.Sequence<byte> _rhs14 = @_302_windowchain;
          @_303_w = _rhs14;
          { }
        }
        else
        {
          if ((@_298_dict).@Contains(@_303_w))
          {
            { }
            Dafny.Sequence<Dafny.Sequence<byte>> _rhs15 = (@_304_out).@Concat(Dafny.Sequence<Dafny.Sequence<byte>>.FromElements((@_298_dict).Select(@_303_w)));
            @_304_out = _rhs15;
            { }
          }
          BigInteger @_305_auxDict = BigInteger.Zero;
          BigInteger _rhs16 = @_296_dictSize;
          @_305_auxDict = _rhs16;
          Dafny.Sequence<byte> @_306_aux = Dafny.Sequence<byte>.Empty;
          Dafny.Sequence<byte> _rhs17 = Dafny.Sequence<byte>.FromElements();
          @_306_aux = _rhs17;
          { }
          while ((@_305_auxDict) >= (new BigInteger(256)))
          {
            Dafny.Sequence<byte> _rhs18 = (Dafny.Sequence<byte>.FromElements((byte)(Dafny.Helpers.EuclideanModulus(@_305_auxDict, new BigInteger(256))))).@Concat(@_306_aux);
            @_306_aux = _rhs18;
            BigInteger _rhs19 = Dafny.Helpers.EuclideanDivision(@_305_auxDict, new BigInteger(256));
            @_305_auxDict = _rhs19;
            { }
          }
          Dafny.Sequence<byte> _rhs20 = (Dafny.Sequence<byte>.FromElements((byte)(@_305_auxDict))).@Concat(@_306_aux);
          @_306_aux = _rhs20;
          Dafny.Map<Dafny.Sequence<byte>,Dafny.Sequence<byte>> _rhs21 = (@_298_dict).Update(@_302_windowchain, @_306_aux);
          @_298_dict = _rhs21;
          BigInteger _rhs22 = (@_296_dictSize) + (new BigInteger(1));
          @_296_dictSize = _rhs22;
          Dafny.Sequence<byte> _rhs23 = Dafny.Sequence<byte>.FromElements((@bytes)[(int)(@_301_currentByte)]);
          @_303_w = _rhs23;
          { }
        }
        System.Console.Write(Dafny.Sequence<BigInteger>.FromElements(@_301_currentByte));
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        BigInteger _rhs24 = (@_301_currentByte) + (new BigInteger(1));
        @_301_currentByte = _rhs24;
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Finish encoding cycle"));
      { }
      if ((new BigInteger((@_303_w).Length)) != (new BigInteger(0)))
      {
        Dafny.Sequence<Dafny.Sequence<byte>> _rhs25 = (@_304_out).@Concat(Dafny.Sequence<Dafny.Sequence<byte>>.FromElements((@_298_dict).Select(@_303_w)));
        @_304_out = _rhs25;
      }
      BigInteger @_307_cal = BigInteger.Zero;
      BigInteger _rhs26 = @_296_dictSize;
      @_307_cal = _rhs26;
      BigInteger @_308_countHelper = BigInteger.Zero;
      BigInteger _rhs27 = new BigInteger(1);
      @_308_countHelper = _rhs27;
      while ((@_307_cal) >= (new BigInteger(256)))
      {
        BigInteger _rhs28 = Dafny.Helpers.EuclideanDivision(@_307_cal, new BigInteger(256));
        @_307_cal = _rhs28;
        BigInteger _rhs29 = (@_308_countHelper) + (new BigInteger(1));
        @_308_countHelper = _rhs29;
      }
      BigInteger @_309_j = BigInteger.Zero;
      BigInteger _rhs30 = new BigInteger(0);
      @_309_j = _rhs30;
      Dafny.Sequence<byte> @_310_encoded = Dafny.Sequence<byte>.Empty;
      if ((new BigInteger((Dafny.Helpers.SeqFromArray(@bytes)).Length)) > (new BigInteger(0)))
      {
        Dafny.Sequence<byte> _rhs31 = Dafny.Sequence<byte>.FromElements((@bytes)[(int)(new BigInteger(0))]);
        @_310_encoded = _rhs31;
      }
      { }
      BigInteger _rhs32 = @_308_countHelper;
      @_297_codelen = _rhs32;
      { }
      Dafny.Sequence<byte> @_311_auxencoded = Dafny.Sequence<byte>.Empty;
      Dafny.Sequence<byte> _rhs33 = Dafny.Sequence<byte>.FromElements();
      @_311_auxencoded = _rhs33;
      while ((@_309_j) < (new BigInteger((@_304_out).Length)))
      {
        Dafny.Sequence<byte> _rhs34 = Dafny.Sequence<byte>.FromElements();
        @_311_auxencoded = _rhs34;
        BigInteger _rhs35 = @_308_countHelper;
        @_297_codelen = _rhs35;
        { }
        if ((new BigInteger(((@_304_out).Select(@_309_j)).Length)) < (@_308_countHelper))
        {
          while ((new BigInteger(((@_304_out).Select(@_309_j)).Length)) < (@_308_countHelper))
          {
            Dafny.Sequence<byte> _rhs36 = (@_311_auxencoded).@Concat(Dafny.Sequence<byte>.FromElements(0));
            @_311_auxencoded = _rhs36;
            BigInteger _rhs37 = (@_308_countHelper) - (new BigInteger(1));
            @_308_countHelper = _rhs37;
            { }
          }
        }
        Dafny.Sequence<byte> _rhs38 = (@_311_auxencoded).@Concat((@_304_out).Select(@_309_j));
        @_311_auxencoded = _rhs38;
        Dafny.Sequence<byte> _rhs39 = (@_310_encoded).@Concat(@_311_auxencoded);
        @_310_encoded = _rhs39;
        { }
        BigInteger _rhs40 = (@_309_j) + (new BigInteger(1));
        @_309_j = _rhs40;
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Finish Padding"));
      { }
      byte[] _out0;
      @__default.@ArrayFromSeq<byte>(@_310_encoded, out _out0);
      @compressed__bytes = _out0;
      { }
      { }
    }
    public static void @decompress__impl(byte[] @compressed__bytes, out byte[] @bytes)
    {
      @bytes = (byte[])null;
    TAIL_CALL_START: ;
      byte[] _rhs41 = @compressed__bytes;
      @bytes = _rhs41;
    }
    public static void @Main()
    {
    TAIL_CALL_START: ;
      uint @_312_numArgs = 0;
      uint _out1;
      @HostConstants.@NumCommandLineArgs(out _out1);
      @_312_numArgs = _out1;
      if ((@_312_numArgs) < (4U))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Not enough arguments, it requires 3"));
      }
      bool @_313_compress = false;
      bool _rhs42 = false;
      @_313_compress = _rhs42;
      bool @_314_uncompress = false;
      bool _rhs43 = false;
      @_314_uncompress = _rhs43;
      int @_315_bufferSize = 0;
      BigInteger @_316_writeBufferSize = BigInteger.Zero;
      int _rhs45 = 0;
      int _rhs44 = _rhs45;
      BigInteger _rhs47 = new BigInteger(0);
      BigInteger _rhs46 = _rhs47;
      @_315_bufferSize = _rhs44;
      @_316_writeBufferSize = _rhs46;
      bool @_317_sucessLen = false;
      bool _rhs48 = false;
      @_317_sucessLen = _rhs48;
      char[] @_318_original = (char[])null;
      char[] _out2;
      @HostConstants.@GetCommandLineArg(2UL, out _out2);
      @_318_original = _out2;
      char[] @_319_copy = new char[0];
      char[] _out3;
      @HostConstants.@GetCommandLineArg(3UL, out _out3);
      @_319_copy = _out3;
      char[] @_320_arg = (char[])null;
      char[] _out4;
      @HostConstants.@GetCommandLineArg(1UL, out _out4);
      @_320_arg = _out4;
      bool _rhs49 = (Dafny.Helpers.SeqFromArray(@_320_arg)).@Equals((Dafny.Sequence<char>.FromString("1")));
      @_314_uncompress = _rhs49;
      bool _rhs50 = (Dafny.Helpers.SeqFromArray(@_320_arg)).@Equals((Dafny.Sequence<char>.FromString("0")));
      @_313_compress = _rhs50;
      { }
      { }
      bool @_321_OriginalExist = false;
      bool _out5;
      @FileStream.@FileExists(@_318_original, out _out5);
      @_321_OriginalExist = _out5;
      if (!(@_321_OriginalExist))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Original file not found..."));
      }
      { }
      bool @_322_CopyExist = false;
      bool _out6;
      @FileStream.@FileExists(@_319_copy, out _out6);
      @_322_CopyExist = _out6;
      { }
      if (@_322_CopyExist)
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Destination file already exists"));
      }
      if (((@_321_OriginalExist) && (!(@_322_CopyExist))) && ((@_314_uncompress) || (@_313_compress)))
      {
        bool _out7;
        int _out8;
        @FileStream.@FileLength(@_318_original, out _out7, out _out8);
        @_317_sucessLen = _out7;
        @_315_bufferSize = _out8;
      }
      @FileStream @_323_originalStream = default(@FileStream);
      @FileStream @_324_copyStream = default(@FileStream);
      bool @_325_successOriginal = false;
      bool @_326_successCopy = false;
      bool _rhs52 = false;
      bool _rhs51 = _rhs52;
      bool _rhs54 = false;
      bool _rhs53 = _rhs54;
      @_325_successOriginal = _rhs51;
      @_326_successCopy = _rhs53;
      bool @_327_successRead = false;
      bool @_328_successWrite = false;
      bool _rhs56 = false;
      bool _rhs55 = _rhs56;
      bool _rhs58 = false;
      bool _rhs57 = _rhs58;
      @_327_successRead = _rhs55;
      @_328_successWrite = _rhs57;
      bool @_329_successClose = false;
      bool @_330_successCloseCopy = false;
      bool _rhs60 = false;
      bool _rhs59 = _rhs60;
      bool _rhs62 = false;
      bool _rhs61 = _rhs62;
      @_329_successClose = _rhs59;
      @_330_successCloseCopy = _rhs61;
      if ((@_317_sucessLen) && (!(@_322_CopyExist)))
      {
        byte[] @_331_buffer = (byte[])null;
        var _nw0 = new byte[(int)(@_315_bufferSize)];
        @_331_buffer = _nw0;
        bool _out9;
        @FileStream _out10;
        @FileStream.@Open(@_318_original, out _out9, out _out10);
        @_325_successOriginal = _out9;
        @_323_originalStream = _out10;
        if (@_325_successOriginal)
        {
          bool _out11;
          @FileStream _out12;
          @FileStream.@Open(@_319_copy, out _out11, out _out12);
          @_326_successCopy = _out11;
          @_324_copyStream = _out12;
          if (@_326_successCopy)
          {
            bool _out13;
            (@_323_originalStream).@Read(0, @_331_buffer, 0, @_315_bufferSize, out _out13);
            @_327_successRead = _out13;
            { }
            if (@_327_successRead)
            {
              byte[] @_332_buffer2 = (byte[])null;
              if (@_313_compress)
              {
                byte[] _out14;
                @__default.@compress__impl(@_331_buffer, out _out14);
                @_332_buffer2 = _out14;
              }
              else
              {
                byte[] _out15;
                @__default.@decompress__impl(@_331_buffer, out _out15);
                @_332_buffer2 = _out15;
              }
              bool _out16;
              (@_324_copyStream).@Write(0, @_332_buffer2, 0, new BigInteger((Dafny.Helpers.SeqFromArray(@_332_buffer2)).Length), out _out16);
              @_328_successWrite = _out16;
              if (@_328_successWrite)
              {
                bool _out17;
                (@_323_originalStream).@Close(out _out17);
                @_329_successClose = _out17;
                if (@_329_successClose)
                {
                  bool _out18;
                  (@_324_copyStream).@Close(out _out18);
                  @_330_successCloseCopy = _out18;
                  if (@_330_successCloseCopy)
                  {
                    System.Console.Write(Dafny.Sequence<char>.FromString("DONE!"));
                  }
                }
              }
            }
          }
        }
      }
      if (((!(@_330_successCloseCopy)) && (@_321_OriginalExist)) && (!(@_322_CopyExist)))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Something went wrong"));
      }
    }
    public static void @ArrayFromSeq<@A>(Dafny.Sequence<@A> @s, out @A[] @a)
    {
      @a = new @A[0];
    TAIL_CALL_START: ;
      var _nw1 = new @A[(int)(new BigInteger((@s).Length))];
      var _arrayinit0 = Dafny.Helpers.Id<@Func<Dafny.Sequence<@A>,@Func<BigInteger,@A>>>((@_333_s) => (@_334_i) => (@_333_s).Select(@_334_i))(@s);
      for (int _arrayinit_00 = 0; _arrayinit_00 < _nw1.Length; _arrayinit_00++) {
        _nw1[_arrayinit_00] = _arrayinit0(_arrayinit_00);
      }
      @a = _nw1;
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
