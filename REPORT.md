# Answers

1. In functions the memory allocation allowed to read is limited, and since in this case there are structures being accessed it is important to add their memory location to the reading frame and this done with command 'read'.
The reason why 'this' is added is because in these functions, the structureswe are accessing are the classes that they belong to, hence the need to provide the location in memory of the instance.

2. If it was possible to create a new FileSystemState object, it would create consistency problems because there would exist multiple states for the same filesystem and creating a file in one filesystem, wouldn't create the same file in another even though they both represent the same filesystem.

3. Preconditions in the Main method define what are the valid inputs with which the method can ensure its functionality. For example in the copy utility we can't ensure that a copy will be successful when the original file doesn't exist. But this input can still made.
