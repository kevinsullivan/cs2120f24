/-!
## The Nat Type and its Value Constructors

UNDER CONSTRUCTION: NO GUARANTEES

Nat is a type, the terms of which have been designed for the
express purpose of representing natural numbers, the infinite
set of whole numbers from zero on up by ones.
-/


/-!
Here is the intended correspondence:

0   Nat.zero
1   Nat.succ Nat.zero
2   Nat.succ (Nat.succ Nat.zero)
3   Nat.succ (Nat.succ (Nat.succ Nat.zero))
etc

The *constant* term, Nat.zero, is taken to represent the natural
number, 0. Lean provides the notation, 0, for Nat.zero, and it is
important to use 0 instead of Nat.zero to take advantage of some
Lean capabilities when we get further into proofs.

The second, one-argument constructor, Nat.succ : Nat → Nat, takes
any natural number, let's call it n', as an argument, and yields the
term, (Nat.succ n'), which we will take to represent one more than n'.
We will call one more than n'the *successor* of n'

When writing Lean definitions it's best to write n' + 1 rather
than (Nat.succ n') to take advantage of certain automations later
on. Using the notations 0 and _ + 1 also makes definitions easier
to read for most people.
-/
