// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract?
  Contract(
    Requires(
      y >= 0
    ),
    Ensures(
      Res[Z] == x*y
    ),
  )

  var total: Z = 0
  var i: Z = 0

  //what goes here?
  //base case: prove the invariant(s) hold initially

  Deduce(
    1 ( total == 0 ) by Premise,
    2 ( i == 0 ) by Premise,
    3 ( total == i*x ) by Algebra*(1, 2)
  ) 
  //need: total == i*x
  
  

  while (i != y) {
    //what goes here?
    Invariant(
      Modifies(total, i),
      //summarizes the progress so far
      //relates the values of variables to each other
      //often looks similar to the postcondition
      total == i*x
    )

    Deduce(
      1 ( total == i*x ) by Premise //like inductive hypothesis
    )

    total = total + x

    Deduce(
      1 ( total == Old(total) + x ) by Premise,
      2 ( Old(total) == i*x ) by Premise,
      3 ( total == i*x + x ) by Algebra*(1,2)
    )

    i = i + 1

    Deduce(
      1 ( total == Old(i)*x + x ) by Premise,
      2 ( i == Old(i) + 1 ) by Premise,
      3 ( Old(i) == i - 1) by Algebra*(2),
      4 ( total == (i-1)*x + x ) by Algebra*(1, 3),
      5 ( total == i*x - x + x ) by Algebra*(4),
      6 ( total == i*x ) by Algebra*(5)
    )

    //what should we be able to assert here?
  }

  //what do we need here?

  Deduce(
    1 ( total == i*x ) by Premise,
    2 ( !(i != y) ) by Premise,
    3 ( i == y ) by Algebra*(2),
    4 ( total == x*y ) by Algebra*(1,3)
  )


  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

Deduce(
  1 ( b == 4 ) by Premise,
  2 ( b >= 0 ) by Algebra*(1)
)

var ans: Z = mult(a, b)

Deduce(
    1 ( ans == a * b ) by Premise,
    2 ( a == 5 ) by Premise,
    3 ( b == 4 ) by Premise,
    4 ( ans == 20 ) by Algebra*(1,2,3)
  )

//what do we want to assert that ans is?
assert(ans == 20)