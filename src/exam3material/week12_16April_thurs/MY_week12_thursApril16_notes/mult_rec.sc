// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  Contract(
    Requires(
      y >= 0
    ),
    Ensures(
      Res[Z] == x*y
    ),
  )
  //what should we require?
  //what should we ensure?

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    Deduce(
      1 ( y == 0 ) by Premise,
      2 ( answer == 0 ) by Premise,
      3 ( y >= 0 ) by Premise,
      4 ( answer == x * y ) by Algebra*(1, 2)
    )

    //what do we need to do here?
  } else {
    //prove precondition for recursive call

    Deduce(
      1 ( y >= 0 ) by Premise, //precondition from current call
      2 ( !(y == 0) ) by Premise, //if condition is false,
      3 ( y != 0 ) by Algebra*(2),
      4 ( y >= 1 ) by Algebra*(1, 3),
      5 ( y - 1 >= 0 ) by Algebra*(4)
    )

    var temp: Z = mult(x, y-1)
    answer = x + temp

    Deduce(
      1 ( temp == x*(y-1) ) by Premise,
      2 ( answer == x + temp ) by Premise,
      3 ( temp == x*y - x ) by Algebra*(1),
      4 ( answer == x + x * y - x ) by Algebra*(2, 3),
      5 ( answer == x*y ) by Algebra*(4)
    )
    //what do we need to show here?
  }

  //what do we need to do here?

  Deduce(
    1 ( answer == x*y ) by Premise,
  )

  return answer
}

////////////// Test code //////////////

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