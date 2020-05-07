# Proofs about Programs, Part 2

So far we've proved the correctness of recursive functions on natural numbers.
We used OCaml's `int` type as a representation of the naturals.  Of course,
that type is somewhat of a mismatch:  negative `int` values don't represent
naturals, and there is an upper bound to what natural numbers we can represent
with `int`.

## Natural Numbers

Let's fix those problems by defining our own variant to represent natural
numbers:
```
type nat = 
  | Z
  | S of nat
```

The constructor `Z` represents zero; and the constructor `S` represents the
successor of another natural number.  So, 

- 0 is represented by `Z`,
- 1 by `S Z`,
- 2 by `S (S Z)`,
- 3 by `S (S (S Z))`, 

and so forth.  This variant is thus a *unary* (as opposed to binary
or decimal) representation of the natural numbers:  the number of times `S`
occurs in a value `n : nat` is the natural number that `n` represents.

We can define addition on natural numbers with the following function:
```
let rec plus a b = 
  match a with
  | Z -> b
  | S k -> S (plus k b)
```

Immediately we can prove the following rather trivial claim:

```
Claim:  plus Z n = n

Proof:

  plus Z n
=   { evaluation }
  n

QED
```

But suppose we want to prove this also trivial-seeming claim:

```
Claim:  plus n Z = n

Proof:

  plus n Z
= 
  ???
```

We can't just evaluate `plus n Z`, because `plus` matches against its first
argument, not second.  One possibility would be to do a case analysis:
what if `n` is `Z`, vs. `S k` for some `k`?  Let's attempt that.

```
Proof:

By case analysis on n, which must be either Z or S k.

Case:  n = Z

  plus Z Z
=   { evaluation }
  Z

Case:  n = S k

  plus (S k) Z
=   { evaluation }
  S (plus k Z)
=
  ???
```

We are again stuck, and for the same reason:  once more `plus` can't be
evaluated any further.

When you find yourself needing to solve the same subproblem in programming,
you use recursion.  When it happens in a proof, you use induction!  

## Induction on nat

We need to do induction on values of type `nat`.  We'll need an induction
principle.  Here it is:
```
forall properties P,
  if P(Z),
  and if forall k, P(k) implies P(S k),
  then forall n, P(n)
```

Compare that to the induction principle we used for natural numbers before,
when we were using `int` in place of natural numbers:
```
forall properties P,
  if P(0),
  and if forall k, P(k) implies P(k + 1),
  then forall n, P(n)
```

There's no essential difference between the two: we just use `Z` in place of
`0`, and `S k` in place of `k + 1`.

Using that induction principle, we can carry out the proof:

```
Claim:  plus n Z = n

Proof: by induction on n.
P(n) = plus n Z = n

Base case: n = Z
Show: plus Z Z = Z

  plus Z Z
=   { evaluation }
  Z

Inductive case: n = S k
IH: plus k Z = k
Show: plus (S k) Z = S k

  plus (S k) Z
=   { evaluation }
  S (plus k Z)
=   { IH }
  S k

QED
```

## Lists

It turns out that natural numbers and lists are quite similar, when viewed
as data types.  Here are the definitions of both, side-by-side for comparison:
```
type 'a list =                  type nat =
  | []                            | Z
  | (::) of 'a * 'a list          | S of nat
```

Both types have a constructor representing a concept of "nothing".  Both types
also have a constructor representing "one more" than another value of the type:
`S n` is one more than `n`, and `h :: t` is a list with one more element than
`t`.

The induction principle for lists is likewise quite similar to the induction
principle for natural numbers.  Here is the principle for lists:
```
forall properties P,
  if P([]),
  and if forall h t, P(t) implies P(h :: t),
  then forall lst, P(lst)
```

An inductive proof for lists therefore has the following structure:
```
Proof: by induction on lst.
P(lst) = ...

Base case: lst = []
Show: P([])

Inductive case: lst = h :: t
IH: P(t)
Show: P(h :: t)
```

Let's try an example of this kind of proof.  Recall the definition of the
append operator:

```
let rec append lst1 lst2 =
  match lst1 with
  | [] -> lst2
  | h :: t -> h :: append t lst2

let (@) = append
```
We'll prove that append is associative.

```
Theorem: forall xs ys zs, xs @ (ys @ zs) = (xs @ ys) @ zs

Proof: by induction on xs.
P(xs) = forall ys zs, xs @ (ys @ zs) = (xs @ ys) @ zs

Base case: xs = []
Show: forall ys zs, [] @ (ys @ zs) = ([] @ ys) @ zs

  [] @ (ys @ zs)
=   { evaluation }
  ys @ zs
=   { evaluation }
  ([] @ ys) @ zs

Inductive case: xs = h :: t
IH: forall ys zs, t @ (ys @ zs) = (t @ ys) @ zs
Show: forall ys zs, (h :: t) @ (ys @ zs) = ((h :: t) @ ys) @ zs

  (h :: t) @ (ys @ zs) 
=   { evaluation }
  h :: (t @ (ys @ zs))
=   { IH }
  h :: ((t @ ys) @ zs)

  ((h :: t) @ ys) @ zs
=   { evaluation of inner @ }
  (h :: (t @ ys)) @ zs
=   { evaluation of outer @ }  
  h :: ((t @ ys) @ zs)

QED
```

## A Theorem about Folding

When we studied `List.fold_left` and `List.fold_right`, we discussed how they
sometimes compute the same function, but in general do not.  For example,

```
  List.fold_left (+) 0 [1; 2; 3]  
= (((0 + 1) + 2) + 3
= 6
= 1 + (2 + (3 + 0))
= List.fold_right (+) lst [1;2;3]
```

but

```
  List.fold_left (-) 0 [1;2;3]
= (((0 - 1) - 2) - 3
= -6
<> 2
= 1 - (2 - (3 - 0))
= List.fold_right (-) lst [1;2;3]
```

Based on the equations above, it looks like the fact that `+` is commutative and
associative, whereas `-` is not, explains this difference between when the two
fold functions get the same answer.  Let's prove it!

First, recall the definitions of the fold functions:
```
let rec fold_left f acc lst =
  match lst with
  | [] -> acc
  | h :: t -> fold_left f (f acc h) t

let rec fold_right f lst acc =
  match lst with
  | [] -> acc
  | h :: t -> f h (fold_right f t acc)
```

Second, recall what it means for a function `f : 'a -> 'a` to be commutative
and associative:
```
Commutative:  forall x y, f x y = f y x  
Associative:  forall x y z, f x (f y z) = f (f x y) z
```
Those might look a little different than the normal formulations of those
properties, because we are using `f` as a prefix operator.  If we were to write
`f` instead as an infix operator `op`, they would look more familiar:
```
Commutative:  forall x y, x op y = y op x  
Associative:  forall x y z, x op (y op z) = (x op y) op z
```
When `f` is both commutative and associative we have this little interchange
lemma that lets us swap two arguments around:
```
Lemma (interchange): f x (f y z) = f y (f x z)

Proof:

  f x (f y z)
=   { associativity }
  f (f x y) z
=   { commutativity }
  f (f y x) z
=   { associativity }
  f y (f z x) 

QED
```

Now we're ready to state and prove the theorem.
```
Theorem: If f is commutative and associative, then
  forall lst acc, 
    fold_left f acc lst = fold_right f lst acc.

Proof: by induction on lst.
P(lst) = forall acc, 
  fold_left f acc lst = fold_right f lst acc

Base case: lst = []
Show: forall acc, 
  fold_left f acc [] = fold_right f [] acc

  fold_left f acc []
=   { evaluation }
  acc
=   { evaluation }
  fold_right f [] acc

Inductive case: lst = h :: t
IH: forall acc, 
  fold_left f acc t = fold_right f t acc
Show: forall acc, 
  fold_left f acc (h :: t) = fold_right f (h :: t) acc

  fold_left f acc (h :: t)
=   { evaluation }
  fold_left f (f acc h) t
=   { IH with acc := f acc h }
  fold_right f t (f acc h)

  fold_right f (h :: t) acc
=   { evaluation }
  f h (fold_right f t acc)
```

Now, it might seem as though we are stuck: the left and right sides of the
equality we want to show have failed to "meet in the middle."  But we're
actually in a similar situation to when we proved the correctness of `facti`
earlier: there's something (applying `f` to `h` and another argument) that we
want to push into the accumulator of that last line (so that we have `f acc h`).

Let's try proving that with its own lemma:
```
Lemma: forall lst acc x, 
  f x (fold_right f lst acc) = fold_right f lst (f acc x)

Proof: by induction on lst.
P(lst) = forall acc x, 
  f x (fold_right f lst acc) = fold_right f lst (f acc x)

Base case: lst = []
Show: forall acc x, 
  f x (fold_right f [] acc) = fold_right f [] (f acc x)

  f x (fold_right f [] acc)
=   { evaluation }
  f x acc

  fold_right f [] (f acc x)
=   { evaluation }
  f acc x
=   { commutativity of f }
  f x acc

Inductive case: lst = h :: t
IH: forall acc x, 
  f x (fold_right f t acc) = fold_right f t (f acc x)
Show: forall acc x, 
  f x (fold_right f (h :: t) acc) = fold_right f (h :: t) (f acc x)

  f x (fold_right f (h :: t) acc)
=  { evaluation }
  f x (f h (fold_right f t acc))
=  { interchange lemma }
  f h (f x (fold_right f t acc))
=  { IH }
  f h (fold_right f t (f acc x))

  fold_right f (h :: t) (f acc x)
=   { evaluation }
  f h (fold_right f t (f acc x))

QED
```

Now that the lemma is completed, we can resume the proof of the theorem.
We'll restart at the beginning of the inductive case:
```
Inductive case: lst = h :: t
IH: forall acc, 
  fold_left f acc t = fold_right f t acc
Show: forall acc, 
  fold_left f acc (h :: t) = fold_right f (h :: t) acc

  fold_left f acc (h :: t)
=   { evaluation }
  fold_left f (f acc h) t
=   { IH with acc := f acc h }
  fold_right f t (f acc h)

  fold_right f (h :: t) acc
=   { evaluation }
  f h (fold_right f t acc)
=   { lemma with x := h and lst := t }
  fold_right f t (f acc h)

QED
```

It took two inductions to prove the theorem, but we succeeded!  Now we know that
the behavior we observed with `+` wasn't a fluke: any commutative and
associative operator causes `fold_left` and `fold_right` to get the same answer.

## Binary Trees

Lists and binary trees are similar when viewed as data types.  Here are the
definitions of both, side-by-side for comparison:
```
type 'a bintree =                           type 'a list =
  | Leaf                                      | []
  | Node of 'a bintree * 'a * 'a bintree      | (::) of 'a * 'a list
```
Both have a constructor that represents "empty", and both have a constructor
that combines a value of type `'a` together with another instance of the
data type.  The only real difference is that `(::)` takes just *one* list,
whereas `Node` takes *two* trees.

The induction principle for binary trees is therefore very similar to the
induction principle for lists, except that with binary trees we get
*two* inductive hypotheses, one for each subtree:
```
forall properties P,
  if P(Leaf),
  and if forall l v r, (P(l) and P(r)) implies P(Node (l, v, r)),
  then forall t, P(t)
```

An inductive proof for binary trees therefore has the following structure:
```
Proof: by induction on t.
P(t) = ...

Base case: t = Leaf
Show: P(Leaf)

Inductive case: t = Node (l, v, r)
IH1: P(l)
IH2: P(r)
Show: P(Node (l, v, r))
```

Let's try an example of this kind of proof.  Here is a function that
creates the mirror image of a tree, swapping its left and right subtrees
at all levels:
```
let rec reflect = function
  | Leaf -> Leaf
  | Node (l, v, r) -> Node (reflect r, v, reflect l)
```

For example, these two trees are reflections of each other:
```
     1               1
   /   \           /   \
  2     3         3     2
 / \   / \       / \   / \
4   5 6   7     7   6 5   4
```

If you take the mirror image of a mirror image, you should get the original
back.  That means reflection is an *involution*, which is any function `f`
such that `f (f x) = x`.  Another example of an involution is multiplication
by negative one on the integers.

Let's prove that `reflect` is an involution.

```
Claim: forall t, reflect (reflect t) = t

Proof: by induction on t.
P(t) = reflect (reflect t) = t

Base case: t = Leaf
Show: reflect (reflect Leaf) = Leaf

  reflect (reflect Leaf)
=   { evaluation }
  reflect Leaf
=   { evaluation }
  Leaf

Inductive case: t = Node (l, v, r)
IH1: reflect (reflect l) = l
IH2: reflect (reflect r) = r
Show: reflect (reflect (Node (l, v, r))) = Node (l, v, r)

  reflect (reflect (Node (l, v, r)))
=   { evaluation }
  reflect (Node (reflect r, v, reflect l))
=   { evaluation }
  Node (reflect (reflect l), v, reflect (reflect r))
=   { IH1 }
  Node (l, v, reflect (reflect r))
=   { IH2 }
  Node (l, v, r)

QED
```

Induction on trees is really no more difficult than induction on lists
or natural numbers.  Just keep track of the inductive hypotheses, using
our stylized proof notation, and it isn't hard at all.

## Induction for Any Data Type

We've now seen induction principles for `nat`, `list`, and `bintree`.
Generalizing from what we've seen, each constructor of a variant either
generates a base case for the inductive proof, or an inductive case. And, if a
constructor itself carries values of that data type, each of those values
generates in inductive hypothesis.  For example:

- `Z`, `[]`, and `Leaf` all generated base cases.

- `S`, `::`, and `Node` all generated inductive cases.

- `S` and `::` each generated one IH, because each carries one value of the
  data type.

- `Node` generated two IHs, because it carries two values of the data type.

Suppose we have these types to represent the AST for expressions in a simple
language with integers, Booleans, unary operators, and binary operators:
```
type uop =
  | UMinus

type bop =
  | BPlus
  | BMinus

type expr =
  | Int of int
  | Bool of bool
  | Unop of uop * expr
  | Binop of expr * bop * expr
```

The induction principle for `expr` is:
```
forall properties P,
  if forall i, P(Int i)
  and forall b, P(Bool b)
  and forall u e, P(e) implies P(Unop (u, e))
  and forall b e1 e2, (P(e1) and P(e2)) implies P(Binop (e1, b, e2))
  then forall e, P(e)
```
There are two base cases, corresponding to the two constructors that don't carry
an `expr`.  There are two inductive cases, corresponding to the two constructors
that do carry `expr`s.  `Unop` gets one IH, whereas `Binop` gets two IHs,
because of the number of `expr`s that each carries.

## Algebraic Specifications

Now that we are proficient at proofs about functions, we can tackle a bigger
challenge:  proving the correctness of a data structure, such as a stack,
queue, or set.

Correctness proofs always need specifications.  In proving the correctness of
iterative factorial, we used recursive factorial as a specification.  By
analogy, we could provide two implementations of a data structure---one simple,
the other complex and efficient---and prove that the two are equivalent.  
That would require us to introduce ways to translate between the two
implementations. For example, we could prove the correctness of a dictionary
implemented as a red-black tree relative to an implementation as an association
list, by defining functions to convert trees to lists.  Such an approach is
certainly valid, but it doesn't lead to new ideas about verification for us
to study.

Instead, we will pursue a different approach based on *equational
specifications*, aka *algebraic specifications*.  The idea with these is to

- define the types of the data structure operations, and 
- to write a set of equations that define how the operations interact with one
  another.

The reason the word "algebra" shows up here is (in part) that this
type-and-equation based approach is something we learned in high-school algebra.
For example, here is a specification for some operators:
```
0 : int
1 : int
- : int -> int
+ : int -> int -> int
* : int -> int -> int

(a + b) + c = a + (b + c)
a + b = b + a
a + 0 = a
a + (-a) = 0
(a * b) * c = a * (b * c)
a * b = b * a
a * 1 = a
a * 0 = 0
a * (b + c) = a * b + a * c
```
The types of those operators, and the associated equations, are facts you
learned when studying algebra.  (And if you take an *abstract algebra* course in
college, you will learn even more about them.)

Our goal is now to write similar specifications for data structures, and
use them to reason about the correctness of implementations.

## Stacks

Here are a few familiar operations on stacks along with their types.
```
module type Stack = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val peek : 'a t -> 'a
  val push : 'a -> 'a t -> 'a t
  val pop : 'a t -> 'a t
end
```
As usual, there is a design choice to be made with `peek` etc. about what to do
with empty stacks.  Here we have not used `option`, which suggests that `peek`
will raise an exception on the empty stack.  So we are cautiously relaxing
our prohibition on exceptions.

In the past we've given these operations specifications in English, e.g.,
```
  (* [push x s] is the stack [s] with [x] pushed on the top *)
  val push : 'a -> 'a stack -> 'a stack
```

But now, we'll instead write some equations to describe how the operations
work:
```
1. is_empty empty = true
2. is_empty (push x s) = false
3. peek (push x s) = x
4. pop (push x s) = s
```
(Later we'll return to the question of *how* to design such equations.)
The variables appearing in these equations are implicitly universally
quantified. Here's how to read each equation:

1. `is_empty empty = true`.  The empty stack is empty.
2. `is_empty (push x s) = false`.  A stack that has just been pushed is
   non-empty.
3. `peek (push x s) = x`.  Pushing then immediately peeking yields whatever
   value was pushed.
4. `pop (push x s) = s`.  Pushing then immediately popping yields the original
   stack.

Just with these equations alone, we already can infer a lot about how any
sequence of stack operations must work.  For example,
```
  peek (pop (push 1 (push 2 empty)))
=   { equation 4 }
  peek (push 2 empty)
=   { equation 3 }
  2
```
And `peek empty` doesn't equal any value according to the equations, since there
is no equation of the form `peek empty = ...`.  All that is true regardless of
the stack implementation that is chosen:  any correct implementation must cause
the equations to hold.

Suppose we implemented stacks as lists, as follows:
```
module ListStack = struct
  type 'a t = 'a list
  let empty = []
  let is_empty s = (s = [])
  let peek = List.hd
  let push = List.cons
  let pop = List.tl
end
```

Next we could *prove* that each equation holds of the implementation.  All these
proofs are quite easy by now, and proceed entirely by evaluation.  For example,
here's a proof of equation 3:
```
  peek (push x s)
=   { evaluation }
  peek (x :: s)
=   { evaluation }
  x
```

## Queues

Stacks were easy.  How about queues?  Here is the specification:

```
module type Queue = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val front : 'a t -> 'a
  val enq : 'a -> 'a t -> 'a t
  val deq : 'a t -> 'a t
end

1.  is_empty empty = true
2.  is_empty (enq x q) = false
3a. front (enq x q) = x            if is_empty q = true
3b. front (enq x q) = front q      if is_empty q = false
4a. deq (enq x q) = empty          if is_empty q = true
4b. deq (enq x q) = enq x (deq q)  if is_empty q = false
```

The types of the queue operations are actually identical to the types
of the stack operations.  Here they are, side-by-side for comparison:
```
module type Stack = sig            module type Queue = sig
  type 'a t                          type 'a t
  val empty : 'a t                   val empty : 'a t
  val is_empty : 'a t -> bool        val is_empty : 'a t -> bool
  val peek : 'a t -> 'a              val front : 'a t -> 'a
  val push : 'a -> 'a t -> 'a t      val enq : 'a -> 'a t -> 'a t
  val pop : 'a t -> 'a t             val deq : 'a t -> 'a t
end                                end
```
Look at each line:  though the operation may have a different name, its type
is the same.  Obviously, the types alone don't tell us enough about the
operations.  But the equations do.  Here's how to read each equation:

1. The empty queue is empty.
2. Enqueueing makes a queue non-empty.
3. Enqueueing `x` on an empty queue makes `x` the front element.
   But if the queue isn't empty, enqueueing doesn't change the front element.
4. Enqueueing then dequeueing on an empty queue leaves the queue empty.
   But if the queue isn't empty, the enqueue and dequeue operations can
   be swapped.

For example,
```
  front (deq (enq 1 (enq 2 empty)))
=   { equation 4b }
  front (enq 1 (deq (enq 2 empty)))
=   { equation 4a }
  front (enq 1 empty)
=   { equation 3a }
  1
```
And `front empty` doesn't equal any value according to the equations.

Implementing a queue as a list results in an implementation that is
easy to verify just with evaluation.
```
module ListQueue : Queue = struct
  type 'a t = 'a list
  let empty = []
  let is_empty q = q = []
  let front = List.hd
  let enq x q = q @ [x]
  let deq = List.tl
end
```

For example, 4a can be verified as follows:
```
  deq (enq x empty) 
=   { evaluation of empty and enq}
  deq ([] @ [x])
=   { evaluation of @ }
  deq [x]
=   { evaluation of deq }
  []
=   { evaluation of empty }
  empty
```

And 4b, as follows:
```
  deq (enq x q) 
=  { evaluation of enq and deq }
  List.tl (q @ [x])
=  { lemma, below, and q <> [] }
  (List.tl q) @ [x]

  enq x (deq q)
=  { evaluation }
  (List.tl q) @ [x]
```

Here is the lemma:
```
Lemma: if xs <> [], then List.tl (xs @ ys) = (List.tl xs) @ ys.
Proof: if xs <> [], then xs = h :: t for some h and t.

  List.tl ((h :: t) @ ys)
=   { evaluation of @ }
  List.tl (h :: (t @ ys))
=   { evaluation of tl }
  t @ ys

  (List.tl (h :: t)) @ ys
=   { evaluation of tl }
  t @ ys

QED
```

Note how the precondition in 3b and 4b of `q` not being empty ensures
that we never have to deal with an exception being raised in the
equational proofs.

## Two-list Queues

Here is our old friend, the two-list queue:
```
module TwoListQueue = struct
  (* AF: (f, b) represents the queue f @ (List.rev b).
     RI: given (f, b), if f is empty then b is empty. *)
  type 'a t = 'a list * 'a list

  let empty = [], []

  let is_empty (f, _) = 
    f = []

  let enq x (f, b) =
    if f = [] then [x], []
    else f, x :: b

  let front (f, _) = 
    List.hd f 

  let deq (f, b) =
    match List.tl f with
    | [] -> List.rev b, []
    | t -> t, b
end
```
This implementation is superficially different from the previous implementation
we gave, in that it uses pairs instead of records, and it in-lines the `norm`
function.  These changes will make our proofs a little easier.

Is this implementation correct?  We need only verify the equations to find out.
Here they are again, for reference.

```
1.  is_empty empty = true
2.  is_empty (enq x q) = false
3a. front (enq x q) = x            if is_empty q = true
3b. front (enq x q) = front q      if is_empty q = false
4a. deq (enq x q) = empty          if is_empty q = true
4b. deq (enq x q) = enq x (deq q)  if is_empty q = false
```

First, a lemma:
```
Lemma:  if is_empty q = true, then q = empty.
Proof:  Since is_empty q = true, it must be that q = (f, b) and f = [].
By the RI, it must also be that b = [].  Thus q = ([], []) = empty.
QED
```

Verifying 1:
```
  is_empty empty
=   { eval empty }
  is_empty ([], [])
=   { eval is_empty }
  [] = []
=   { eval = }
  true
```

Verifying 2:
```
  is_empty (enq x q) = false
=   { eval enq }
  is_empty (if f = [] then [x], [] else f, x :: b)

case analysis: f = []

  is_empty (if f = [] then [x], [] else f, x :: b)
=   { eval if, f = [] }
  is_empty ([x], [])
=   { eval is_empty }
  [x] = []
=   { eval = }
  false

case analysis: f = h :: t

  is_empty (if f = [] then [x], [] else f, x :: b)
=   { eval if, f = h :: t }
  is_empty (h :: t, x :: b)
=   { eval is_empty }
  h :: t = []
=   { eval = }
  false
```

Verifying 3a:
```
  front (enq x q) = x
=   { emptiness lemma }
  front (enq x ([], []))
=   { eval enq }
  front ([x], [])
=   { eval front }
  x
```

Verifying 3b:
```
  front (enq x q)
=   { rewrite q as (h :: t, b), because q is not empty }
  front (enq x (h :: t, b))
=   { eval enq }
  front (h :: t, x :: b)
=   { eval front }
  h

  front q
=   { rewrite q as (h :: t, b), because q is not empty }
  front (h :: t, b)
=   { eval front }
  h
```

Verifying 4a:
```
  deq (enq x q)
=   { emptiness lemma }
  deq (enq x ([], []))
=   { eval enq }
  deq ([x], [])
=   { eval deq }
  List.rev [], []
=   { eval rev }
  [], []
=   { eval empty }
  empty
```

Verifying 4b:
```
Show: deq (enq x q) = enq x (deq q)  assuming is_empty q = false.
Proof: Since is_empty q = false, q must be (h :: t, b).

Case analysis:  t = [], b = []

  deq (enq x q)
=   { rewriting q as ([h], []) }
  deq (enq x ([h], []))
=   { eval enq }
  deq ([h], [x])
=   { eval deq }
  List.rev [x], []
=   { eval rev }
  [x], []

  enq x (deq q)
=   { rewriting q as ([h], []) }
  enq x (deq ([h], []))
=   { eval deq }
  enq x (List.rev [], [])
=   { eval rev }
  enq x ([], [])
=   { eval enq }
  [x], []

Case analysis:  t = [], b = h' :: t'

  deq (enq x q) 
=   { rewriting q as ([h], h' :: t') }
  deq (enq x ([h], h' :: t'))
=   { eval enq }
  deq ([h], x :: h' :: t')
=   { eval deq }
  List.rev (x :: h' :: t'), []

  enq x (deq q)
=   { rewriting q as ([h], h' :: t') }
  enq x (deq ([h], h' :: t'))
=   { eval deq }
  enq x (List.rev (h' :: t'), [])
=   { eval enq }
  (List.rev (h' :: t'), [x])

STUCK
```

Wait, we just got stuck!  `List.rev (x :: h' :: t'), []` and 
`(List.rev (h' :: t'), [x])` are not the same.  But, abstractly, they do
represent the same queue: `(List.rev t') @ [h'; x]`.  We need to allow
an additional equation for the representation type:
```
e = e'   if  AF(e) = AF(e')
```

Using that additional equation, we can continue:
```
  (List.rev (h' :: t'), [x])
=   { AF equation }
  List.rev (x :: h' :: t'), []


The AF equation holds because:

  List.rev (h' :: t') @ [x]
=   { eval rev }
  List.rev (h' :: t') @ List.rev [x]
=   { rev distributes over @, an exercise in the previous lecture }
  List.rev ([x] @ (h' :: t'))
=   { eval @ }
  List.rev (x :: h' :: t'))
=   { lst @ [] = lst, an exercise in the previous lecture }
  List.rev (x :: h' :: t') @ []

Case analysis:  t = h' :: t'

  deq (enq x q)
=   { rewriting q as (h :: h' :: t', b) }
  deq (enq x (h :: h' :: t', b))
=   { eval enq }
  deq (h :: h' :: t, x :: b)
=   { eval deq }
  h' :: t, x :: b

  enq x (deq q)
=   { rewriting q as (h :: h' :: t', b) }
  enq x (deq (h :: h' :: t', b))
=   { eval deq }
  enq x (h' :: t', b)
=   { eval enq }
  h' :: t', x :: b

QED
```

That concludes our verification of the two-list queue.  Note that
we had to add the extra equation involving the abstraction function
to get the proofs to go through:
```
e = e'   if  AF(e) = AF(e')
```
and that we made use of the RI during the proof.  The AF and RI
really are important!

## Designing the Equations

For both stacks and queues we provided some equations as the specification.
Designing those equations is, in part, a matter of thinking hard about
the data structure.  But there's more to it than that.

Every value of the data structure is constructed with some operations. For a
stack, those operations are `empty` and `push`.  There might be some `pop`
operations involved, but those can be eliminated.  For example, `pop (push 1
(push 2 empty))` is really the same stack as `push 2 empty`. The latter is the
*canonical form* of that stack:  there are many other ways to construct it, but
that is the simplest.  Indeed, every possible stack value can be constructed
just with `empty` and `push`.  Similarly, every possible queue value can
be constructed just with `empty` and `enq`:  if there are `deq` operations
involved, those can be eliminated.

Let's categorize the operations of a data structure as follows:

- **Generators** are those operations involved in creating a canonical form.
  They return a value of the data structure type.  For example,
  `empty`, `push`, `enq`.

- **Manipulators** are operations that create a value of the data structure
  type, but are not needed to create canonical forms.  For example,
  `pop`, `deq`.

- **Queries** do not return a value of the data structure type.  For example,
  `is_empty`, `peek`, `front`.

Given such a categorization, we can design the equational specification of
a data structure by applying non-generators to generators.  For example:
What does `is_empty` return on `empty`? on `push`? What does `front` return
on `enq`? What does `deq` return on `enq`? etc.

So if there are `n` generators and `m` non-generators of a data structure, we
would begin by trying to create `n*m` equations, one for each pair of a
generator and non-generator.  Each equation would show how to simplify an
expression.  In some cases we might need a couple equations, depending on the
result of some comparison.  For example, in the queue specification, we have the
following equations:

1. `is_empty empty = true`:  this is a non-generator `is_empty` applied to a
   generator `empty`.  It reduces just to a Boolean value, which doesn't 
   involve the data structure type (queues) at all.

2. `is_empty (enq x q) = false`:  a non-generator `is_empty` applied to a
   generator `enq`.  Again it reduces simply to a Boolean value.

3. There are two subcases.
   - `front (enq x q) = x`, if `is_empty q = true`.  A non-generator `front`
     applied to a generator `enq`.  It reduces to `x`, which is a smaller
     expression than the original `front (enq x q)`.
   - `front (enq x q) = front q`, `if is_empty q = false`.  This similarly
     reduces to a smaller expression.

4. Again, there are two subcases.
   - `deq (enq x q) = empty`, if `is_empty q = true`.  This simplifies
     the original expression by reducing it to `empty`.
   - `deq (enq x q) = enq x (deq q)`, if `is_empty q = false`.  This simplifies
     the original expression by reducing it to an generator applied to a
     smaller argument, `deq q` instead of `deq (enq x q)`.

We don't usually design equations involving pairs of non-generators.  Sometimes
pairs of generators are needed, though, as we will see in the next example.

## Sets

Here is a small interface for sets:
```
module type Set = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val add : 'a -> 'a t -> 'a t
  val mem : 'a -> 'a t -> bool
  val remove : 'a -> 'a t -> 'a t
end
```

The generators are `empty` and `add`.  The only manipulator is `remove`.
Finally, `is_empty` and `mem` are queries.  So we should expect at least 2 * 3 =
6 equations, one for each pair of generator and non-generator. Here is an
equational specification:

```
1.  is_empty empty = true
2.  is_empty (add x s) = false
3.  mem x empty = false
4a. mem y (add x s) = true                    if x = y
4b. mem y (add x s) = mem y s                 if x <> y
5.  remove x empty = empty
6a. remove y (add x s) = remove y s           if x = y
6b. remove y (add x s) = add x (remove y s)   if x <> y
```

Consider, though, these two sets:
- `add 0 (add 1 empty)`
- `add 1 (add 0 empty)`

They both intuitively represent the set {0,1}.  Yet, we cannot prove
that those two sets are equal using the above specification.  We are
missing an equation involving two generators:

```
7.  add x (add y s) = add y (add x s)
```

## Exercises

### Exercise 1

Prove that `forall n, mult n Z = Z` by induction on `n`, where:
```
let rec mult a b =
  match a with
  | Z -> Z
  | S k -> plus b (mult k b)
```

### Exercise 2

Prove that `forall lst, lst @ [] = lst` by induction on `lst`.

### Exercise 3

Prove that reverse distributes over append, i.e., that
`forall lst1 lst2, rev (lst1 @ lst2) = rev lst2 @ rev lst1`, where:
```
let rec rev = function
  | [] -> []
  | h :: t -> rev t @ [h]
```
(That is, of course, an inefficient implemention of `rev`.) You will need
to choose which list to induct over.  You will need the previous exercise
as a lemma, as well as the associativity of `append`, which was proved in the
notes above.

### Exercise 4

Prove that reverse is an involution, i.e., that 
  `forall lst, rev (rev lst) = lst`.
Proceed by induction on `lst`. You will the previous exercise as a lemma.

### Exercise 5

Prove that `forall t, size (reflect t) = size t` by induction on `t`, where:
```
let rec size = function
  | Leaf -> 0
  | Node (l, v, r) -> 1 + size l + size r
```

### Exercise 6

In propositional logic, we have propositions, negation, conjunction,
disjunction, and implication.  The following BNF describes propositional
logic formulas:
```
p ::= atom
    | ~ p      (* negation *)
    | p /\ p   (* conjunction *)
    | p \/ p   (* disjunction *)
    | p -> p   (* implication *)

atom ::= <identifiers>
```
For example, `raining /\ snowing /\ cold` is a proposition stating that it is
simultaneously raining and snowing and cold (a weather condition known 
as *Ithacating*).

Define an OCaml type to represent the AST of propositions.  Then state
the induction principle for that type.

### Exercise 7

A *bag* or *multiset* is like a blend of a list and a set:  like a set, order
does not matter; like a list, elements may occur more than once.  The number of
times an element occurs is its *multiplicity*.  An element that does not occur
in the bag has multiplicity 0. Here is an OCaml signature for bags:
```
module type Bag = sig
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val insert : 'a -> 'a t -> 'a t
  val mult : 'a -> 'a t -> int
  val remove : 'a -> 'a t -> 'a t
end
```

Categorize the operations in the `Bag` interface as generators, manipulators,
or queries.  Then design an equational specification for bags.  For the `remove`
operation, your specification should cause at most one occurrence of an element
to be removed.  That is, the multiplicity of that value should decrease
by at most one.

### Exercise 8

Design an OCaml interface for lists that has `nil`, `cons`, `append`,
and `length` operations.  Design the equational specification. Hint:
the equations will look strikingly like the OCaml implementations of
`@` and `List.length`.


## Solutions

### Exercise 1

```
Claim: forall n, mult n Z = Z
Proof: by induction on n
P(n) = mult n Z = Z

Base case: n = Z
Show: mult Z Z = Z

  mult Z Z
=   { eval mult }
  Z
  
Inductive case: n = S k
Show: mult (S k) Z = Z
IH: mult k Z = Z

  mult (S k) Z
=   { eval mult }
  plus Z (mult k Z)
=   { IH }
  plus Z Z
=   { eval plus }
  Z
  
QED
```

### Exercise 2

```
Claim:  forall lst, lst @ [] = lst
Proof: by induction on lst
P(lst) = lst @ [] = lst

Base case: lst = []
Show: [] @ [] = []

  [] @ []
=   { eval @ }
  []

Inductive case: lst = h :: t
Show: (h :: t) @ [] = h :: t
IH: t @ [] = t

  (h :: t) @ []
=   { eval @ }
  h :: (t @ [])
=   { IH }
  h :: t

QED
```

### Exercise 3

```
Claim: forall lst1 lst2, rev (lst1 @ lst2) = rev lst2 @ rev lst1
Proof: by induction on lst1
P(lst1) = forall lst2, rev (lst1 @ lst2) = rev lst2 @ rev lst1

Base case: lst1 = []
Show: forall lst2, rev ([] @ lst2) = rev lst2 @ rev []

  rev ([] @ lst2)
=   { eval @ }
  rev lst2

  rev lst2 @ rev []
=   { eval rev }
  rev lst2 @ []
=   { exercise 2 }
  rev lst2
  
Inductive case: lst1 = h :: t
Show: forall lst2, rev ((h :: t) @ lst2) = rev lst2 @ rev (h :: t)
IH: forall lst2, rev (t @ lst2) = rev lst2 @ rev t

  rev ((h :: t) @ lst2)
=   { eval @ }
  rev (h :: (t @ lst2))
=   { eval rev }
  rev (t @ lst2) @ [h]
=   { IH }
  (rev lst2 @ rev t) @ [h]
  
  rev lst2 @ rev (h :: t)
=   { eval rev }
  rev lst2 @ (rev t @ [h])
=   { associativity of @, proved in notes above }
  (rev lst2 @ rev t) @ [h]
  
QED
```

### Exercise 4

```
Claim: forall lst, rev (rev lst) = lst
Proof: by induction on lst
P(lst) = rev (rev lst) = lst

Base case: lst = []
Show: rev (rev []) = []

  rev (rev []) 
=   { eval rev, twice }
  []
  
Inductive case: lst = h :: t
Show: rev (rev (h :: t)) = h :: t
IH: rev (rev t) = t

  rev (rev (h :: t))
=   { eval rev }
  rev (rev t @ [h])
=   { exercise 3 }
  rev [h] @ rev (rev t)
=   { IH }
  rev [h] @ t
=   { eval rev }
  [h] @ t
=   { eval @ }
  h :: t
  
QED
```

## Exercise 5 

```
Claim: forall t, size (reflect t) = size t
Proof: by induction on t
P(t) = size (reflect t) = size t

Base case: t = Leaf
Show: size (reflect Leaf) = size Leaf

  size (reflect Leaf)
=   { eval reflect }
  size Leaf

Inductive case: t = Node (l, v, r)
Show: size (reflect (Node (l, v, r))) = size (Node (l, v, r))
IH1: size (reflect l) = size l
IH2: size (reflect r) = size r

  size (reflect (Node (l, v, r)))
=   { eval reflect }
  size (Node (reflect r, v, reflect l))
=   { eval size }
  1 + size (reflect r) + size (reflect l)
=   { IH1 and IH2 }
  1 + size r + size l

  size (Node (l, v, r))
=   { eval size }
  1 + size l + size r
=   { algebra }
  1 + size r + size l

QED
```

## Exercise 6

```
type prop = (* propositions *)
  | Atom of string
  | Neg of prop
  | Conj of prop * prop
  | Disj of prop * prop
  | Imp of prop * prop

Induction principle for prop:

forall properties P,
  if forall x, P(Atom x)
  and forall q, P(q) implies P(Neg q)
  and forall q r, (P(q) and P(r)) implies P(Conj (q,r))
  and forall q r, (P(q) and P(r)) implies P(Disj (q,r))
  and forall q r, (P(q) and P(r)) implies P(Imp (q,r))
  then forall q, P(q)
```

### Exercise 7

Generators: `empty`, `insert`.  Manipulator: `remove`.  Queries: `is_empty`, 
`mult`.

Specification:
```
1.  is_empty empty = true
2.  is_empty (insert x b) = false
3.  mult x empty = 0
4a. mult y (insert x b) = 1 + mult y b              if x = y
4b. mult y (insert x b) = mult y b                  if x <> y
5.  remove x empty = empty
6a. remove y (insert x b) = b                       if x = y
6b. remove y (insert x b) = insert x (remove y b)   if x <> y
7.  insert x (insert y b) = insert y (insert x b)
```

### Exercise 8

Operations:
```
module type List = sig
  type 'a t
  val nil : 'a t
  val cons : 'a -> 'a t -> 'a t
  val append : 'a t -> 'a t -> 'a t
  val length : 'a t -> int
end
```

Equations:
```
1. append nil lst = lst
2. append (cons h t) lst = cons h (append t lst)
3. length nil = 0
4. length (cons h t) = 1 + length t
```

## Acknowledgements

- *The Functional Approach to Programming*, section 3.4.  Guy Cousineau and
  Michel Mauny. Cambridge, 1998.

- *ML for the Working Programmer*, second edition, chapter 6.  L.C. Paulson.
  Cambridge, 1996.

- *Thinking Functionally with Haskell*, chapter 6.  Richard Bird.  Cambridge,
  2015.

- *Software Foundations*, volume 1, chapters Basic, Induction, Lists, Poly.
  Benjamin Pierce et al. https://softwarefoundations.cis.upenn.edu/
  
- Course materials for Princeton COS 326 by David Walker et al.

- "Algebraic Specifications", Robert McCloskey, 
  https://www.cs.scranton.edu/~mccloske/courses/se507/alg_specs_lec.html.

- *Software Engineering: Theory and Practice*, third edition, section 4.5.
  Shari Lawrence Pfleeger and Joanne M. Atlee.  Prentice Hall, 2006.

- "Algebraic Semantics", chapter 12 of *Formal Syntax and Semantics of
  Programming Languages*, Kenneth Slonneger and Barry L. Kurtz, Addison-Wesley,
  1995.

- "Algebraic Semantics", Muffy Thomas.  Chapter 6 in *Programming Language
  Syntax and Semantics*, David Watt, Prentice Hall, 1991.

- *Fundamentals of Algebraic Specification 1: Equations and Initial Semantics*.
  H. Ehrig and B. Mahr.  Springer-Verlag, 1985.

The example specifications above are based on McCloskey.  The
terminology of "generator", "manipulator", and "query" is based on
Pfleeger and Atlee.
