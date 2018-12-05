/*
 * This is the skeleton for your cp utility.
 *
 * Rui Maranhao -- rui@computer.org
 */

include "Io.dfy"

// Useful to convert Dafny strings into arrays of characters.
method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  requires |env.constants.CommandLineArgs()|>= 3
  modifies env.ok
  modifies env.files
{
  //adicionar throw a erro caso não haja argumentos suficientes.
  var orignal := HostConstants.GetCommandLineArg(1,env);
  var copy := HostConstants.GetCommandLineArg(2,env);



    print "done!\n";
}
