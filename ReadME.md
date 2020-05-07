
For this project we decided to implement the language features of runtime checking, or dynamic indexing with vectors. 
For our approach, we first decided to begin by thinking of how to increment and adjust a vector with the appending items. After discussing our project with our Professor Near, we decided it would be best to shift our approach to implement structure similar to linked lists. When making our compiler, we initially based it on assignment 6 and then added our R5 and TypedR5 expressions of the con, car, cdr and nil functions.

Linked List Example:
let ls = vector(1, vector(2, nil))
in vectorRef(vectorRef(ls, 1), 0)


These features that we implemented include appending items together which is outlined in the implementation of the con function. We were also able to provide functionality for returning both the head item implemented as car and the tail items of the list, the cdr function. All of these abilities allow our linked list to be constructed from the ListT type in the R4 language. All of these functionalities can be expressed in terms of the ListT type which are in the end called as functions in the x86 code. 


We planned to implement our functions more, but because of many outside constraints, we were unable to finish full implemenation. We worked to better our implementation by testing our work against test cases. We had some difficulties with certain test cases (specifically test case 70 and cases with lambdas). Overall, we worked hard with the time that we had. 


