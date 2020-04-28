We will implement runtime checking with vectors and dynamic indexing by a dynamic heap for effective implementation of dynamic allocation.

Notes from Project Meeting: 

simplest linked list is 
let ls = vector(1, vector(2, nil))
in vectorRef(vectorRef(ls, 1), 0)



Challenge in typechecker, as you cannot write type of linked list in vector terms(recursive)
Make "List" type for typechecking. File in the cases too
