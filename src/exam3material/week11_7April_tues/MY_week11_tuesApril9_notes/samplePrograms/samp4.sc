// #Sireum #Logika
//@Logika: --manual

import org.sireum._

//write a separate function to add all elements in a sequence
//create a sequence, call the function, print the result
//ZS is sequence of integers
def sumSequence(seq: ZS) : Z = { //the letter after the : is the return type
  var sum: Z = 0

  var i: Z = 0

  while (i < seq.size) {
    sum = sum + seq(i)
    i = i + 1
  }

  return sum
}

//////////////////

val list: ZS = ZS(1,2,3,4) //defines a list
val total: Z = sumSequence(list)
println("Sum of elements:", total)