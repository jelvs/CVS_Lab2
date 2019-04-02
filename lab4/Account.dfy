/**
    ©João Costa Seco, Eduardo Geraldo, CVS, FCT NOVA, MIEI 2018
    This is the forth lab assignment for the Construction and Verification of
    Software of the integrated master in computer science and engineering
    (MIEI) http://www.di.fct.unl.pt/miei

    The piazza page where you can discuss solutions and problems related to
    this lab class is at: https://piazza.com/class/jt9v3bajo03e3#

    Your mission is to specify and implement the Account ADT.
	  For the methods' specifications write the weakest pre-condition and the
	  strongest post-condition possible. Implement and verify the methods 
  	according to that same specification.
	
	  The class Account represents a bank account.  On this account it is
    to deposit and withdraw money.
 */
class Account {
  
  var balance:int;

  
  /**
    Returns the balance.
    Suggestion: implement as a function method so it can be called
	  both in methods and specs.
   */
  function method Balance(): int

  //this pode ser omitido( mas ser o mais especifico possivel)
  reads this `balance
  {
    balance
  }

  function RepInv(): bool
  reads this `balance
  {
    0 <= balance
  }

   /**
    Specify and implement the constructor of the class.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
  */
  constructor()
  ensures RepInv()
  {
    balance := 0;
  }

  /**
    Specify and implement method deposit below. The functionality of this method
    emulates the a deposit operation on bank account. As such, this
    operation increases the balance of the account according
    to the amount withdrawed.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
  */
  method deposit(amount:int)
  requires RepInv() && 0 <= amount
  ensures RepInv()
  modifies this `balance
  {
    balance := balance + amount;
  }

  /**
    Specify and implement method withdraw below. The functionality of this method
    emulates a withdrawl operation on bank account. As such, this
    operation reduces the balance of the account accodring
    to the amount withdrawed. Take note that the account balance
    should always be non-negative.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
  */
  method withdraw(amount:int)
  requires RepInv() && 0 <= amount <= Balance()
  ensures RepInv()
  modifies this `balance
  {
    balance := balance - amount;
  }

  /**
    Main method. Creates an account and executes deposit and
    withdrawl operation on it. This method does not require
    annspecificationsotations, you just have tom implement it.
	  Use this to test our ADT.
	    <var acc:Account := new Account();>
   */
  method main(){
    var a:Account := new Account();
    a.deposit(10);
    if( 10 <= a.Balance()){
      a.withdraw(10);
    }
  }
}