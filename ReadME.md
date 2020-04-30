We will implement runtime checking with vectors and dynamic indexing by a dynamic heap for effective implementation of dynamic allocation.

Project Construction/Notes
Notes from Project Meeting: 

simplest linked list is 
let ls = vector(1, vector(2, nil))
in vectorRef(vectorRef(ls, 1), 0)

Challenge in typechecker, as you cannot write type of linked list in vector terms(recursive).
Make "List" type for typechecking. Fill in the type-check cases as needed. 

