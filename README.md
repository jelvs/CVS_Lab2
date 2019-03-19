

# Dafny

## Dafny Guide : http://rise4fun.com/Dafny/tutorial/guide

Dafny is a programming language developed by Microsoft Research; it has built-in specification constructs which allow for the static formal verification of programs functional correctness (the programs do what they are supposed to do) the code produced. To specify a Dafny program, it is necessary to define the methods' preconditions and postconditions. Assuming the preconditions of a method, Dafny will try to prove then postconditions based on the method's body; if it cannot prove the postconditions, then the program is not correct since it does not comply with its specification.

