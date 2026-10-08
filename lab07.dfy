/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 7  (Week 9) -- Loops That Stop
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running.

   Dafny checks the whole file continuously. 
   
   An unfinished or incorrect definition shows a red squiggle and a 
   message in the Problems pane. The lab-work you need to do is to 
   fill every hole so the file is error-free: every method defined, 
   every claim checked by Dafny.
*/

// ******** Q1
/* Add an invariant and a decreases clause (only; don't touch the 
   code) so that Dafny accepts the method.  Then answer in a comment:
   what goes wrong if the precondition is weakened to just a <= b?
   Give a concrete input.
*/
method meet(a:int, b:int) returns (m:int)
  requires a <= b && (b - a) % 3 == 0
{
    var x, y := a, b;
    while x != y
    decreases y - x
    // decreases y
    invariant (y - x) % 3 == 0
    invariant x <= y
    {
        x := x + 2;
        y := y - 1;
    }
    m := x;
}


// ******** Q2
/* A bag holds red and blue balls.  Each step either removes a blue 
   ball, or (if there are no blues) removes a red ball and throws in 
   as many blue balls as it likes.  

   The line  var k:nat :| true; is what does the "throws in as many 
   blue balls as it likes"; it picks an ARBITRARY natural number
   for k: Dafny must check the loop works whatever k turns out to be.

   Add a decreases clause so that the method verifies.
*/
method balls(r0:nat, b0:nat)
{
    var red:nat, blue:nat := r0, b0;
    while red > 0 || blue > 0
    decreases red , blue
    {
        if blue > 0 {
            blue := blue - 1;
        } else {
            red := red - 1;
            var k:nat :| true;
            blue := k;
        }
    }
}

// ******** Q3
/* The same bag, but now at most K blue balls can be added at a 
   time.  This time, give a decreases clause that is a SINGLE number
   (no commas).  Then answer in a comment (talk to your tutor about 
   this): why can't you do the same for Q2?
*/
method balls_bounded(r0:nat, b0:nat, K:nat)
{
    var red:nat, blue:nat := r0, b0;
    while red > 0 || blue > 0
    decreases red, blue
    {
        if blue > 0 {
            blue := blue - 1;
        } else {
            red := red - 1;
            var k:nat :| k <= K;
            blue := k;
        }
    }
}


// ******** Q4
/* A sequence of natural numbers is processed from the front.  Take
   off the first element h; if h is positive, put h-1 back on the 
   front.  The sum function comes after the method.

   Add a decreases clause so that the method verifies.  Then answer
   in a comment and talk to your tutor: why does neither |q| nor 
   sum(q) work on its own?
*/
method countdown_stack(q0:seq<nat>)
{
    var q := q0;
    while |q| > 0
    decreases |q| , sum(q)
    {
        var h := q[0];
        if h > 0 {
            q := [h - 1] + q[1..];
        } else {
            q := q[1..];
        }
    }
}

function sum(s:seq<nat>) : nat
{
    if s == [] then 0 else s[0] + sum(s[1..])
}

// ******** Q5 (TOUGH EXTENSION)
/* As Q4, but now h-1 goes on the BACK of the sequence.  The same 
   decreases clause should do, but Dafny can no longer see that it
   goes down.  You will need to call the sum_append lemma (after the 
   method) in the code, and then make sum_append itself verify.
*/
method countdown_queue(q0:seq<nat>)
{
    var q := q0;
    while |q| > 0
    decreases |q|
    decreases sum(q)
    {
        var h := q[0];
        if h > 0 {
            sum_append(q[1..] , h-1);
            q := q[1..] + [h - 1];
        } else {
            q := q[1..];
        }
        
    }
    
}

lemma sum_append(s:seq<nat>, x:nat)
  ensures sum(s + [x]) == sum(s) + x
{
    if s == [] {
    } else {
        assert s +[x] == [s[0]] + (s[1..] + [x]);
    }
}


