/* ============================================================
   COMP1600 / COMP6260  Foundations of Computing
   Lab 3  (Week 4) -- Data Structures, Contracts and Termination
   Covers material from Lectures 6 and 7.
   ============================================================

   HOW TO USE THIS FILE
   --------------------
   Open this file in VS Code with the Dafny extension running. A red
   squiggle in the Problems pane means there is work to do.

   This lab is more open than the last two. In Part A you define set
   operations and then state and prove the lemmas that CHARACTERISE how
   they behave (plus one requires-guard). Part B is a bigger piece of
   work: a binary search tree. You are given ONLY English descriptions
   there; translating them into Dafny -- choosing the signatures, the
   bodies, and the lemma statements -- is the exercise.

   Two of the Part B lemmas will NOT go green with an empty  {}  body.
   That is deliberate: they are a first look at proofs, which we take up
   properly next. Each is flagged where it appears.

   Part C (Lecture 7) is an EXTENSION on termination. Items marked (*)
   are stretch goals. Ask questions early and often.
   ============================================================ */


// -------- Given infrastructure (from earlier weeks / Lecture 6) --------

datatype list<T> = Nil | Cons(hd : T, tl : list<T>)


type lset = list<int>   // a set of ints, stored as a list

function length<T>(l : list<T>) : nat
{
  match l
  case Nil => 0
  case Cons(_, xs) => 1 + length(xs)
}

function append<T>(l1 : list<T>, l2 : list<T>) : list<T>
{
  match l1
  case Nil => l2
  case Cons(x, xs) => Cons(x, append(xs, l2))
}

function member(x : int, l : list<int>) : bool
{
  match l
  case Nil => false
  case Cons(y, ys) => x == y || member(x, ys)
}

// Two already-proved helper lemmas you may CALL later if you need them.
lemma lengthAppend<T>(l1 : list<T>, l2 : list<T>)
  ensures length(append(l1, l2)) == length(l1) + length(l2)
{}

lemma member_append(x : int, l1 : list<int>, l2 : list<int>)
  ensures member(x, append(l1, l2)) <==> member(x, l1) || member(x, l2)
{}


/* ------------------------------------------------------------
   PART A -- Set operations and their characterising lemmas
                                                 (Lecture 6)
   ------------------------------------------------------------ */

// Exercise 1.
// insert(x, A) adds x to the set A -- just put it on the front.
function insert(x : int, A : lset) : lset
{
  Cons(x,A)
}
// TODO: give a body


// Exercise 2.
// delete(x, A) removes EVERY copy of x from A.
function delete(x : int, A : lset) : lset
{
  match A
  case Nil => Nil
  case Cons(h,t) => if x == h then delete(x,t) else Cons(h,delete(x,t))
}
// TODO: give a body


// Exercise 3.
// anyElement(A) returns some element of A. This only makes sense when A
// is non-empty -- otherwise there is no element and  A.hd  is not valid.
// Add a  requires  that rules the empty case out, then return  A.hd .
function anyElement(A : lset) : int
  requires A != Nil
{
  A.hd
}
// TODO: add a  requires , then a body


// Exercise 4.
// The lemma that says exactly what insert does to membership: some x is
// a member of  insert(y, A)  precisely when x is the newly-inserted y,
// or x was already a member of A. Write the ensures; {} proves it.
lemma member_insert(x : int, y : int, A : lset)
  ensures member(x, insert(y, A)) <==> x == y || member(x,A)
  // TODO: write the ensures  ( member(x, insert(y, A)) <==> ... )
{}


// Exercise 5.
// And the matching lemma for delete: x is a member of  delete(y, A)
// precisely when x is not the deleted y, AND x was already a member of A.
lemma member_delete(x : int, y : int, A : lset)
  ensures member(x,delete(y,A)) <==> x != y && member(x,A)
  // TODO: write the ensures
{}


/* ------------------------------------------------------------
   PART B -- Binary search trees   (Lecture 6)
   ------------------------------------------------------------
   You are given the tree type only. Everything else in this part you
   write yourself, from the English. There are no signatures and no
   Dafny below -- work out the types, the bodies and the claims.

   A binary search tree stores integer keys, each with an associated
   value of type V. It is ORDERED: at every node, all keys in the left
   subtree are smaller than the node's key, and all keys in the right
   subtree are larger. (You may assume the trees you are given are
   ordered; you do not have to check it.)
   ------------------------------------------------------------ */

datatype btree<V> = Lf | Node(k : int, value : V, left : btree, right : btree)
datatype option<V> = None | Some(v : V)
// Exercise 6.  Define  size .
//   The number of Node nodes in a tree (a leaf Lf contributes nothing).
function size<V>(t:btree<V>):nat
{
  match t
  case Lf => 0
  case Node(k,v,l,r) => 1 + size(l) + size(r)
}

// Exercise 7.  Define  lookup .
//   Given a tree and a key, return the stored value wrapped as  Some ,
//   or  None  if the key is not in the tree. Use the ordering to search
//   efficiently: compare the wanted key with the node's key -- equal
//   means found; smaller means look in the left subtree; larger means
//   look in the right subtree.
function lookup<V>(key:int,t:btree<V>):option<V>
{
  match t
  case Lf => None
  case Node(k,v,l,r) => if k == key then Some(v)
                        else if k < key then lookup(key,r)
                        else lookup(key,l) 
}

// Exercise 8.  Define tree insertion.
//   Given a key, a value and a tree, return the tree updated so that the
//   key maps to the value. If the key is already present, replace its
//   value; if not, add a new node in the correct ordered position.
//   NOTE: you already used the name  insert  in Part A, and Dafny does
//   not allow two functions with the same name -- call this one something
//   else, e.g.  insertT , and use that name in the lemmas below.
function insertion<V>(key:int,value:V,t:btree<V>):btree<V>
{
  match t
  case Lf => Node(key,value,Lf,Lf)
  case Node(k,v,l,r) => if k == key then Node(key,value,l,r)
                        else if k < key then Node(k,v,l,insertion(key,value,r))
                        else Node(k,v,insertion(key,value,l),r)
}

// Exercise 9.  Define  keys .
//   Return the list of all keys in the tree, in ascending order: the
//   keys of the left subtree, then this node's key, then the keys of the
//   right subtree. (One of the given helpers builds "a followed by b".)
function returnKeys<V>(t:btree<V>):lset
{
  match t
  case Lf => Nil
  case Node(k,v,l,r) => append(returnKeys(l),Cons(k,returnKeys(r)))
}

// -------- Lemmas about the tree operations --------
// State each of these as a lemma and try to prove it. Unless flagged,
// an empty  {}  body should be enough.

// Exercise 10.
//   Looking up a key straight after inserting it with value v returns
//   exactly  Some(v) .
lemma inserting<V>(key:int,value:V,t:btree<V>)
  ensures lookup(key,insertion(key,value,t)) == Some(value)
  {}
// Exercise 11.
//   Looking up a key k2 after inserting a DIFFERENT key k1 gives the
//   same answer as looking up k2 in the original tree. (You will need a
//   precondition saying the two keys differ.)
lemma lookingup<V>(k1:int,k2:int,v1:V,v2:V,t:btree<V>)
  requires k1 != k2
  ensures lookup(k2,t) == lookup(k2,insertion(k1,v1,t)) 
{}
// Exercise 12.
//   Inserting adds at most one node: the size afterwards is no more than
//   one greater than the size before.

// Exercise 13.  ** FLAGGED: {} is NOT enough here. **
//   Inserting a key that was NOT already present increases the size by
//   exactly one. (Express "not already present" using  member  and your
//   keys function.) Try the empty body first and watch it fail -- this
//   is the kind of fact that needs a real proof. If you want to push on,
//   the given lemma  member_append  is the tool that unlocks it.

// Exercise 14.  ** FLAGGED: {} is NOT enough here either **
//   The number of keys of a tree equals its size:  length(keys(t))  is
//   size(t) . The empty body will not close this one either -- to relate
//   the length of the appended key-lists you will need to remind Dafny
//   of the given fact  lengthAppend . (This is a gentle first proof.)


/* ------------------------------------------------------------
   PART C -- Termination and  decreases   (Lecture 7)  (*) EXTENSION
   ------------------------------------------------------------
   Each function below is correct, but recurses by counting a variable
   UP towards a bound. Dafny cannot see why that stops, so it squiggles
   the recursive call ("cannot prove termination"). Add a  decreases
   clause giving a quantity that gets SMALLER each call -- think about
   the gap between the counter and its bound.
   ------------------------------------------------------------ */

// Exercise 15.  (*)
// upList(lo, hi) builds the list  [lo, lo+1, ..., hi-1]  by counting
// upward. Add the  decreases  clause that makes Dafny accept it.
function upList(lo : int, hi : int) : list<int>
  requires lo <= hi
  decreases hi - lo
  // TODO: add a  decreases  clause
{
  if lo == hi then Nil else Cons(lo, upList(lo + 1, hi))
}

// Exercise 16.  (*)
// fib_loop implements a loop for calculating the n-th Fibonacci
// number, so that fib below can run efficiently. But Dafny
// doesn't see that fib_loop must terminate. Indeed, it doesn't, not for 
// all possible arguments.  In the two contexts where it is called 
// (recursively, and where it is started off in the body of fib),
// it will be fine.  So WHY IS THIS???  

// You will need to add a requires clause to encapsulate that.

/* fi = i'th fib number; fpi = fib number of i - 1 ("previous to i") */
function fib_loop(fi : nat, fpi : nat, i : nat, n : nat) : nat
  // TODO: add a decreases *and* a requires clause
  requires n >= i
  decreases n - i
{
  if n == i then fi
  else fib_loop (fi + fpi, fi, i + 1, n)
}

function fib(n:nat) : nat 
  requires n >= 1
  decreases n -1 
{ 
  if n == 0 then 0 
  else fib_loop(1,0,1,n) 
}

// ============================================================
// End of Lab 3. (Parts A and C green; two Part B lemmas are meant
// to resist the empty body -- see you next week for the proofs.)
// ============================================================
