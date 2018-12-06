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
  requires env.constants.CommandLineArgs()[1] in env.files.state()
  requires  env.constants.CommandLineArgs()[2] !in env.files.state()
  modifies env.ok
  modifies env.files 
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[2] in env.files.state();
  ensures env.ok.ok() ==> env.constants.CommandLineArgs()[1] in env.files.state()
  ensures env.ok.ok()  ==> var copyname := env.constants.CommandLineArgs()[2];
          old(env.files.state()) == env.files.state()[copyname:=[]];
  ensures env.ok.ok() ==> copyFile(env.constants.CommandLineArgs()[1],env.constants.CommandLineArgs()[2],env); 
  {
  var bufferSize:=0;
  var sucessLen;
  var original:= env.constants.GetCommandLineArg(1,env);   
   var copy :=env.constants.GetCommandLineArg(2,env);
  sucessLen,bufferSize := FileStream.FileLength(original,env);
  var originalStream, copyStream;
  var successOriginal,successCopy:=false,false;
  var successRead,successWrite := false,false;
   var successClose,successCloseCopy := false,false;
  if(sucessLen){
    var buffer := new  byte[bufferSize];
    successOriginal,originalStream := FileStream.Open(original,env);
    if(successOriginal){
      successCopy,copyStream := FileStream.Open(copy,env);
      if(successCopy){
        successRead := originalStream.Read(0,buffer,0,bufferSize);
        if(successRead){
          successWrite := copyStream.Write(0,buffer,0,bufferSize);         
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

