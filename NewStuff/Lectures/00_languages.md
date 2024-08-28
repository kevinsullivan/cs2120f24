## Languages

Languages are for communicating.

### Natural Language

- English
- Mandarin
- Spanish

#### Natural language is expressive

#### Natural language is ambiguous

Consider a warning sign on escalator: "Shoes must be worn;
Dogs must be carried." How many different meanings could you
possibly attach to this command? Be creative.

Now consider what the words "and" and "or" could mean, in English.
-- Example 1: they got married and they had a baby
-- Example 2: they had a baby and they got married
-- Example 3: You can have a candy or you can have a donut

The first two examples illustrate a meaning for "and" that
involves some notion of temporal ordering. On the other hand,
in the propositional and predicate logic we'll study, "and" has
no such sense, but is true if and only if both arguments are
true. The formal definition of *and* as a function in the same
style as we defined *nand* makes its meaning unambiguous.

In the third example, the dad almost certainly meant
that you can have one or the other but not both. In the
propositional and predicate logics we'll study, an *or*
expression is true if either or both of its arguments
are true. The *exclusive or* (xor) function, on the other
hand, is false when both inputs are true. Is *xor* what
the dad meant?

Did the dad mean that you can have one or the other but
not both *and that you must have at least one*? That'd be
xor, again. But he probably didn't really mean that she
*had to* have at least one sweet. What he really meant
in all likelihood was that it'd be okay ("true") for her
to have none, or one, or the other, but not both. What
logical function captures that idea precisely? Hint:
Compare the output of this function for each case with
the outputs of the *or* function. How do they relate?

The ambiguity of natural language is resolved by giving
"formal," which is to say mathematical, definitions of
terms such as *and* and *or*. And once our informal ideas
are represented formally, we can then apply the amazing
tools of logic and mathematics to reason about them very
precisely.

#### Natural Language is Imprecise

#### Natural Language is Not Computable

- Ambiguous, imprecise, not mechanically checkable for errors
- For problems with diverse, relevant, available communications
- Beyond sophisticated keyword lookup (Google); but unreliable
- LLMs: 
  - unreliable functions from natural language to programs
  - actually wrong: unreliable functions from natural language to programs

### Formal Languages

#### Uses

- Programming languages are formal languages
- Mathematics, and incredible diversity of formal languages
- Logics and Proofs, the quintessential formal languages

#### Imperative vs Declarative Languages

##### Declarative: Abstract specification

Example: for any non-negative real number, r, the square root of r is any number s such that s^2 = r.

##### Imperative: Concrete procedures

Example: a program implementing Newton's method for computing square roots up to a specified precision
