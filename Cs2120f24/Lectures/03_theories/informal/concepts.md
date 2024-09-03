# Theories

## The Idea

### Examples

- equality  
- natural numbers
  rationals
- reals
- characters
- strings
- lists
- bit vectors
- etc.
  
### Case Study Overview: A Natural Number Arithmetic Theory

A theory for our purposes will be a formal language, here again
an expression language, (1) for expressing propositions about values
of and relations involving natural numbers, (2) with an operational
semantics that implements automatic expression evaluation, given an
interpretation assigning values to the *natural number variables* in
such an expression.

For example, given arithmetic variables, N, M, and K, for example,
what is the value of the expression, N? Of K? Of N (add N K), N + K?
To answer these questions we need interpretations. So now suppose an
interpretation, interp_0, is defined to return 0 for N, 0 for K, and
indeed 0 for any variable you apply it to. To evaluate N + K, evaluate
N (0), evaluate K (0), evaluate + (natural number addition function!),
and return the result of applying that function to compose the partial
for N and K into a semantic value for the overall expression.

Ok, yeah, this looks a *lot* like what we just did for propositional
logic. The main complication is that it involves not Bools, with two
possible values for each variable, to Nats (natural numbers), with an
infinite number of values (terms corresponding precisely to the ideal
natural numbers in the minds of mathematicians everywhere).

Of course, the unary and binary operators on numbers are different
from those on Bools. Instead of *or* and *and*, for example, we now
have *add* and *multiply*.

### A Natural Number Arithmetic Expression Language

#### Domnain: The Natural Numbers

We represent them as terms of type Nat.

inductive Nat : Type
| zero
| succ (n' : nat)

- def zero := Nat.zero
- def one' := Nat.succ(zero)
- def one := Nat.succ (Nat.zero)
- def two := Nat.succ one
- etc

#### Analysis

/-
Constructor expression pattern matching with temporary name bindings
-/

def pred : Nat \to Nat
| zero => zero
| (succ n') => n'

#### Operations

##### Arithmetic (\to Nat)

-- unary

- succ :    Nat \to Nat
- pred :    Nat \to Nat
- double :  Nat \to Nat
- square :  Nat \to Nat

-- binary

- add n m : Nat \to Nat \to Nat
- sub n m : Nat \to Nat \to Nat
- mul n m : Nat \to Nat \to Nat
- exp n m : Nat \to Nat \to Nat

##### Boolean (\to Bool, from Nat)

- eq_0 n 
- eq n m
- le n m
- even n
- odd n


Formalizing the semantics of propositional logic was made easier by
the fact that the domain of discourse, the semantic domain, has only
two values: Boolean true and Boolean false. Every knows that a Boolean
variable can have one of only two values, and that we might as well
just call them true and false. 

Now we're in a domain where the values being defined and composed by
various *arithmetic* operators represent natural numbers: values from
the set of all non-negative whole numbers. While everyone has a good
intuition for how to represent a value of type Bool (it can be one of 
only two things), it's less clear how to represent any given natural
number.

#### Constructors Produce/Synthesize Terms (Values) of Given Type

#### Destructuring Consumes/Analyzes Terms Values via Pattern Matching

Constructor Application Patterns



    - Nat
    - increment
    - analyze
    - addition
    - multiplication
    - exponentiation
    - syntax:
      - abstract
      - concrete notations
    - 
  - SMT Solvers: Z3 Python API
- Wecome to abstract thinking!
  