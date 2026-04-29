// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//adult tickets: $50
//kid tickets: $30
def getTicketCosts(adult: Z, kid: Z): Z = {
  //what do we want for our function contract?
  Contract(
    Requires(adult >= 0, kid >= 0),
    Ensures(Res[Z] == 50*adult + 30*kid, Res[Z] >= 0)
  )


  //what to do here?


  //get the total ticket cost
  val overall: Z = adult*50 + kid*30

  //what to do here? 2) and 3)
  Deduce(
    1 ( overall == adult*50 + kid*30 ) by Premise,
    2 ( adult >= 0 ) by Premise,
    3 ( kid >= 0 ) by Premise,
    4 ( overall == 50*adult + 30*kid ) by Algebra*(1),
    5 ( overall >= 0 ) by Algebra*(1, 2, 3)
  )

  return overall
}

////////////// Test code /////////////////

val k: Z = 3 //$30 each
val a: Z = 2 //$50 each

//what to do here?
//1) Prove precondition
Deduce(
  1 ( k == 3 ) by Premise,
  2 ( a == 2 ) by Premise,
  3 ( a >= 0 ) by Algebra*(2),
  4 ( k >= 0 ) by Algebra*(1)
)

val cost: Z = getTicketCosts(a, k)

//what to do here?
Deduce(
  1 ( cost == 50*a + 30*k ) by Premise,
  2 ( k == 3 ) by Premise,
  3 ( a == 2 ) by Premise,
  4 ( cost == 190 ) by Algebra*(1,2,3)
)

//what *should* cost be?
assert(cost == 190)