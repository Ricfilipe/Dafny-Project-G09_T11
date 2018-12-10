/*
 * This is the skeleton for your cp utility.
 *
 * Rui Maranhao -- rui@computer.org
 */

include "Io.dfy"
include "lzw.dfy"

// Useful to convert Dafny strings into arrays of characters.
method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  requires |env.constants.CommandLineArgs()|>=3
  requires if env.constants.CommandLineArgs()[2] in env.files.state() then |env.constants.CommandLineArgs()| >= 4 && env.constants.CommandLineArgs()[3] == "-o"[..] else |env.constants.CommandLineArgs()| >= 3
  requires env.constants.CommandLineArgs()[1] in env.files.state()


  modifies env.ok
  modifies env.files 
  ensures env.ok.ok()  ==> env.constants.CommandLineArgs()[2] in env.files.state();
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[1] in env.files.state()
  ensures env.ok.ok()  ==> var copy := env.constants.CommandLineArgs()[2];
                          var original :=env.constants.CommandLineArgs()[1];
          env.files.state() == old(env.files.state())[copy:= old(env.files.state())[original]];
  ensures env.ok.ok() ==> copyFile(env.constants.CommandLineArgs()[1],env.constants.CommandLineArgs()[2],env); 
  {

  var numArgs :=env.constants.NumCommandLineArgs(env);
  if(numArgs<3){
     print("Not enough arguments, it requires 2");
  }
  var override := false;
  var bufferSize,writeBufferSize:=0,0;
  var sucessLen := false;
  var original:= env.constants.GetCommandLineArg(1,env);   
  var copy :=env.constants.GetCommandLineArg(2,env);
  if(numArgs>=4){
    var arg := env.constants.GetCommandLineArg(3,env);
    override := arg[..] == "-o"[..];
  }
   assert override ==> |env.constants.CommandLineArgs()| >= 4 && env.constants.CommandLineArgs()[3] == "-o"[..];
  var OriginalExist :=FileStream.FileExists(original,env);
  
  if(!OriginalExist){
    print("Original file not found...");
  }
  assert OriginalExist ==> old(env.constants.CommandLineArgs())[1] in env.files.state();
  var CopyExist := FileStream.FileExists(copy,env);
  assert CopyExist ==> old(env.constants.CommandLineArgs())[2] in env.files.state();
  if(CopyExist && !override){
    print("Add -o if you want to override");  
  }

  if(OriginalExist && CopyExist && override) {
    sucessLen,bufferSize := FileStream.FileLength(original,env); 
  }else if(OriginalExist && !CopyExist){
    sucessLen,bufferSize := FileStream.FileLength(original,env);
  }
  var originalStream, copyStream;
  var successOriginal,successCopy:=false,false;
  var successRead,successWrite := false,false;
   var successClose,successCloseCopy := false,false;
  if(sucessLen && (!CopyExist || (CopyExist && override))){
    var buffer := new  byte[bufferSize];
    successOriginal,originalStream := FileStream.Open(original,env);
    if(successOriginal){
      successCopy,copyStream := FileStream.Open(copy,env);
      if(successCopy){
        successRead := originalStream.Read(0,buffer,0,bufferSize);
        assert env.ok.ok() ==> old(env.files.state())[original[..]] == buffer[..];
        if(successRead){
          successWrite := copyStream.Write(0,buffer,0,bufferSize); 
          assert env.ok.ok() ==> env.files.state()[copy[..]] == buffer[..];
          assert env.ok.ok() ==> env.files.state() == old(env.files.state())[copy[..]:=buffer[..]] ; 
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
  
predicate copyFile(original : seq<char>,copy : seq<char>, env: HostEnvironment)
reads env.ok
reads env
reads env.files
requires  env.Valid() 
requires env.ok.ok()
requires original in env.files.state()
requires copy in env.files.state()
{
  env.files.state()[original] == env.files.state()[copy]
}

