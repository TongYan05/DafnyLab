/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 5  (Week 7) -- Imperative Dafny, Loops and Invariants
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   Dafny checks the whole file continuously. 
   
   An unfinished or incorrect definition shows a red squiggle and a 
   message in the Problems pane. YOUR JOB is to fill every hole so 
   the file is error-free: every method defined, every claim checked 
   by Dafny.
*/

// ******** Q1
/* Implement the absolute difference function as a method.
   If m > n then the result is m - n, otherwise it's n - m

   Try implementing with return statements, and by just 
   assigning to return variable 'r'.
*/
method absdiff(m : nat, n : nat) returns (r:nat)
  ensures m > n ==> r == m - n
  ensures n >= m ==> r == n - m
{
  if m > n { r := m - n ;}
  else{r:=n-m;}
}
  
// ******** Q2
// implement a method to return the square of n (i.e., n * n)

// When you've done it the easy, direct way, try doing it with a 
// loop(!), noting that each successive square is separated by 
// successive odd numbers:
//   0  +   1  ==  1
//   1  +   3  ==  4
//   4  +   5  ==  9
//   9  +   7  == 16
//  16  +   9  == 25

// For this question, don't bother with an invariant and just
// test your code with the Main method.  The last question in 
// the lab will ask you to do the full version with invariant
method nthSquare(n:nat) returns (sq:nat)
  ensures sq == n * n
{
  sq := n * n;
}

// to run this you will have to give the loops in Q3 bodies, 
// just {} is fine because those methods aren't called here.
method Main()
{
    var sq3 := nthSquare(3);
    var sq13 := nthSquare(13);
    print "3 * 3 = ", sq3, "\n";
    print "13 * 13 = ", sq13, "\n";
}

// ******** Q3
/* from "Program Proofs": f11_1a and f11_1d, fix the method
   invariants so that Dafny is happy with the assertion
   (what the loop is meant to achieve).
   
   For each, also prove the counter-example lemma, demonstrating
   why the specification is inadequate
   
*/

// Q3A
method f11_1a() returns (i:int)
{
    i := 0;
    while i < 100
      invariant 0 <= i
      // decreases *
      // {}
      {
        i := i + 1;
      }
    assert i == 100;
}

predicate f11_1a_counter_example_pred(i : int)
{
    !(i < 100) &&     // guard is false
    0 <= i &&         // invariant is true
    !(i == 100)       // yet, final assertion not achieved
}

lemma f11_1a_counterexample_lemma()
  ensures exists i : int :: f11_1a_counter_example_pred(i)
{
    // uncomment and insert counter-example value below for XXX
    // assert f11_1a_counter_example_pred(XXX);
    assert f11_1a_counter_example_pred(101);
}

// Q3B
method f11_1d() returns (i:int)
{
    i := 22;
    while i % 5 != 0 invariant 10 <= i <= 100
    // decreases *
    // {}
    {
      i := i + 33;
      break;
    }
    assert i == 55;
}

predicate f11_1d_counterexaple_pred(i:int)
{
    i % 5 == 0 &&       // loop guard is false
    10 <= i <= 100 &&   // invariant still true
    i != 55             // and yet, final goal not achieved
}

lemma f11_1d_counterexample_lemma()
  ensures exists i:int :: f11_1d_counterexaple_pred(i)
{
    // uncomment and insert counter-example value instead of XXX
    //assert f11_1d_counterexaple_pred(XXX);
    assert f11_1d_counterexaple_pred(60);
}

// ******** Q4
/* Write the correct invariant for the loop in fibmd below.
   It has three clauses, each describing something invariant
   about the three variables: smaller, larger and counter.
*/

function fibfn(n:nat) : nat
{   // the Fibonacci function, implemented/specified very
    // inefficiently
    if n < 2 then 1 else fibfn(n-1) + fibfn(n-2) //f2=f1+f0=2  f3=f1+f0+f1=3   f4=f3+f2=4  f5=f4+f3=7 f6=f5+f4=11   1 1 2 3 4 7 11
}

method fibmd(n:nat) returns (r:nat)
  ensures r == fibfn(n)
{
    var smaller, larger, counter := 1, 1, 0;
    while (counter < n) // counter == n-1
      invariant true
      invariant 0 <= counter <=n
      // invariant 1 <= smaller <= larger
      invariant smaller == fibfn(counter)
      invariant larger == fibfn(counter + 1)
      // decreases n - counter
    {
        smaller, larger := larger, smaller + larger;// c=1 s=1   c=2 s=1   c=3 s=2
        counter := counter + 1;
    }
    return smaller;
}

// ******** Q4
/* Give your nthSquare method with a loop an invariant
*/