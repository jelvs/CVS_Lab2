

# Dafny

## Dafny Guide : http://rise4fun.com/Dafny/tutorial/guide

Dafny is a programming language developed by Microsoft Research; it has built-in specification constructs which allow for the static formal verification of programs functional correctness (the programs do what they are supposed to do) the code produced. To specify a Dafny program, it is necessary to define the methods' preconditions and postconditions. Assuming the preconditions of a method, Dafny will try to prove then postconditions based on the method's body; if it cannot prove the postconditions, then the program is not correct since it does not comply with its specification.

Quantifiers are one of the many features supported by Dafny. A quantifier in Dafny most often takes the form of a forall expression, also called a universal quantifier. As its name suggests, this expression is true if some property holds for all elements of some set.


A guide on Dafny quantifiers can be found at : [Click me!](https://rise4fun.com/dafny/tutorialcontent/guide#h28)





