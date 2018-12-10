# Aswers
1. In functions the memory allocation allowed to read is limited and because in this functions, its accessed structures. It's important to add their memory location to the reading 
frame and this done with command 'read'.The reason why its added 'this' is because in this functions, the structure we access are the classes that they belong to. So need to access
memory location of the instance.

2.If it was possible to create a new FileSystemState object, it would create consistency problems because there would have been multiple states for the same filesystem and creating 
a file in one filesystem, wouldn't create file in another even though they both represent the same filesystem.

3. Preconditions in the Main method define what are the inputs that method can ensure its functionality. For example in the copy utility we can't ensure that copy is going to be 
made when original file doesn't exist. But this input can still made.