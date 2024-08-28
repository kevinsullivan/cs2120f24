# DMT1: Discrete Mathematics and Theory

<!--I. From Concrete Programming to Abstract Mathematics  -->

If you understanding Boolean expressions, ubiquitous in everyday
programming, the you understand propositional logic. The concrete
syntax

This is a course in discrete mathematics and structures for
early undergraduate computer science students. It both assumes
and takes advantage of both a student's knowledge of computing, 
from having taken at least one course in programming, and his 
or her intrinsic motivation to learn deep ideas in this area.

To achieve this end, the course takes an approach to teaching
logic, proof, set theory, and beyond, entirely rooted in the 
profound idea that logical reasoning is computation.

- In CS111x you learned to use the concepts, syntax, and meaning of an imperative programming logic
- In this class you will to use learn the concepts, syntax, and meaning of several formal logics, and mathematical concepts that are established directly on these logical foundations
- Traditional courses in DMT teach First-order truth functional predicate logic and set theory
- In this class,, you will learn to think in and use far more expressive language of *type theory*
- You will see how you can use it to specify, implement, and then use many other formal languages
  - propositional logic
  - first-order truth functional predicate logic
  - set theory, including relations and their properties
  - special purpose logics based on your own data types


<!-- LANGUAGES: FORMAL AND INFORMAL -->

## Languages

Natural languages are for communicating. Not so much for
reasoning or computation. It's fabulous for talking about
ideas, telling fictions, explaining things in ways that
people understand nearly automatically -- as long as one
has learned to speak, hear, and perhaps read and write in
a given language.

Proofs as social processes.

### Natural Language

- English
- Mandarin
- Spanish

#### Natural language is highly expressive

#### Natural language is inherently ambiguous

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

#### Natural language is not computable

- Ambiguous, imprecise, insufficiently structured
- LLMs are a step toward synthesis from natural language
- For problems about which there's lots of communication
- A step beyond mere keyword lookup (Google) but unreliable

### Formal Languages

#### Uses

- Logics and programming languages are formal languages
- Geared toward reasoning, including automated, less to communication
- Typically accommodate but ignore embedded NL comments
- Mathematics, and incredible diversity of formal languages
- Mathematicians typically communicate in precise natural language
- Logics and Proofs, these are the quintessential formal languages
- Computer science emerged from logic and proof -- Turing, Church, Shannon

#### Imperative vs Declarative

##### Declarative: Abstract Specification

Example: for any non-negative real number, r, the square root of r is any number s such that s^2 = r.

##### Imperative: Concrete Procedures

Example: a program implementing Newton's method for computing square roots up to a specified precision

#### The *Expressiveness* of a Formal Language

- Declarative languages are generally expressive (what not how) but in general are not computable
- Imperative languages are computable but inscrutable. which is to say, very much less expressive
- There are many abstract/declarative logics of widely varying levels of expressiveness
  - Propositional logic (equivalent to the language of Boolean expressions): not very expressive
  - First-order truth functional predicate logic and set theory: more expressive but also not so much
    - Even some basic concepts can't be expressed: e.g., what it means for a relation to be transitive
  - Type theory (as in Lean):
    - extraordinarily expressive, suitable for formalizing advanced mathematics
    - unifies mathematical logic and computation, *essential* for modern theorem proving

#### Optative vs Indicative Moods

- Indicative: Expression asserts something about the actual state of affairs in some world of interest
- Optative: Expression describes a desired state, that some kind of intervention is meant to establish
- Examples: The cup is on the table. Ind: I'm asserting that's true. Opt: I want you to make it be true.

### Beyond Pseudo-Math

(Intentionally provocative)

Two-by-two grid:

- Natural vs Formal
- Imperative vs Declarative

That gives us the following

- Natural Imperative (Pseudo-code)
- Natural Declarative (Pseudo-math)
- Formal Imperative (Programming)
- Formal Declarative (Specification)


<!-- A Formal Declarative Language : Propositional Logic -->

We promised that we'd move from computational ideas that you
already understand to abstract declarative formal languages of
logic and higher levels of discrete mathematics. We do just 
that here by teaching a very simple lesson: propositional logic
is isomorphic (essentially identical to) Boolean algebra, the
language of Boolean conditions as used in loop conditions and
conditional branching statements in *whatever* language you've
learned as your first programming language. The only difference
is in notations. The underlying concepts are identical. Here we
will treat them with some rigor, elaborate on their uses, and
learn *deep stuff* about critical properties of expressions in
this formal language. 

## A Simple Formal Language For Sound Reasoning

Sound vs unsound.

### Informal Introduction

#### Using Names to Represent Elementary Propositions

#### Inductively Building New Expressions from Given Ones

#### Interpretations and Evaluating Truth of Expressions

### Syntax and Semantics

#### Abstract Syntax

- operator expressions: Not, And, Or, Implies, Iff

##### Constant expressions

⊤ (top),⊥ (bottom)

##### Variable Expressions

- variable expressions: IAmNotBob, SpotIsADog, X, Y, P, Q

##### Logical Operators

- Not _, And _ _, Or _ _, Implies _ _, Iff _ _
- ¬, ∧ ∨ ⇒ ⇔

#### Concrete Syntax

- Left/Right Associativity
- Operator Precedence

### Semantics

#### Interpretations

#### Variable Expressions

#### Logical Operators

#### Truth Tables

### Properties of Expressions

#### Models

#### Validity

#### Satisfiability

#### Unsatisfiability

### Theory Extensions

- Objects (such as numbers, bits, etc.)
- Equality
- Arithmetic
- Lists
- Sets

### SAT and SMT solvers

- Z3
- Dafny

<!-- DATA TYPES AND TERMS -->

## Data Types and Terms

### Introduction

This chapter introduces the concept of types and terms (a.k.a. values),
fundamental in both programming and logic, including, in particular, the
logic of the Lean proof assistant. We will explore these concepts using Lean
itself.

#### Types and Values

#### Types in Computing

- Typed and Untyped Languages
- Static and Dynamic Type Checking

Examples:

- Python: Dynamically type checked only (by default)
- Java: Statically type checked

#### Types in Logic

- Untyped First-Order Set Theory (traditional DM class)
- Type Theory (this class)

Examples:

### Data Types

#### Examples

Enumerated (finite number of terms):

- Bool
- Unit
- Empty

Inductive (possibly infinite number of terms)

- Nat
- String

### Function Types

#### Function Terms

#### Function Application Terms

#### Function Application Notations

Prefix. Infix. Postfix. Outfix.

Precedence. Left and right Associativity.

#### Function Application Evaluation

Beta reduction: specialization, universal instantiation

#### Higher-Order Functions

Function terms are data, too.

#### Partial Evaluation (Specialization)

<!-- BINDING NAMES TO TERMS -->

## Binding Names to Terms

### Identifiers

Every identifier has a single type

### Binding Identifiers to Terms

- Types of terms must match types of identifiers bound to them
- Lean is a simple but extraordinarily useful static type checker

#### Binding Names to Data Terms

#### Binding Names to Function Terms

### Evaluation of Identifier Terms

- Delta reduction
- Examples
  - evaluating individual identifiers
  - evaluating expressions that use identifiers

<!-- GENERALIZATION AND INSTANTIATION -->

## Generalization and Instantiation

### Motivation: Don't Repeat Yourself

### Parametric Polymorphic: Types Arguments

### Instantiation with Partial Evaluation

### Type Inference and Implicit Arguments

### Example: ApplyTwice

<!-- FUNCTIONS AND FUNCTION COMPOSITION -->

## Functions in Predicate Logic and Mathematics

### Indirect References to Other Objects

### Function Definitions are Terms Too

### Function Composition

#### Concrete examples

#### Generalized Mathematical Definition

#### Applying the Generalized Definition

#### New Level of Abstraction

#### Function as Objects

- Akin to numbers 
  
#### Composition as Operator

- Akin to addition or multiplication

<!-- DEFINING DATA AND FUNCTION TYPES AND TERMS -->

We use terms of data types to represent objects in
given domains of discourse. For example, we might use
a term that encodes a pair of values, such as the name
and employee number, for a person who works for some outfit. The data type might be called *EmployeeRecord*, 
while a specific *term* (value), of this type might be 
a pair denoted as ⟨ "Kevin Sullivan", 123456789 ⟩.

## Elements of Type Definitions

- name
- parameters
- type (of the type being defined)
- constructors and resulting terms
- eliminators (functions)

## Types are Terms Too

Types have types, ad infinitum

## The Idea of Types as Propositions (MOVE THIS)

- Represent proposition as types.
- Interpret values as proofs.
- If such a type has a value, it's "true".
- A type with no value (uninhabited) is false.

<!-- PROPOSITIONS AS TYPES -->

## Fundamental Types and Logical Interpretations

### Empty Type

#### Standard Empty Type in Lean

#### An Empty Type as the Proposition, False

#### How To Prove a Proposition is False

This is the "strategy" of proof by negation.

### Unit Type

This is the *void* type in Java and Python.

#### Standard Unit Type in Lean

#### The Unit Type as the Proposition, True

### Bool Type

- An essential enumerated type
- Two constant terms
- Terms (not types) interpreted as Boolean truth values
- Boolean algebra: type, terms, and functions
  - formal and actual arguments
  - elimination by pattern matching
  - pattern matching notations
- Propositional logic: isomorphic to Boolean algebra

### Enumerated Type

- Multiple constant terms
- Use to represent all kinds of simple data values
- Example: representing and computing with days of week

### Box Type
  
- A box holds some other thing
- A terms of type Box holds one term of some other type
- Constructor
- Eliminator

#### Polymorphic Box Type

#### What Does a Term of Type Box α Prove?

#### From Such a Proof What Can We Derive?

#### The Notion of a *Constructive* Proof

### Polymorphic Product Type

- One two-argument constructor
- Can represent logic *and* of two other propositions
- Value can represent a proof of such a proposition
- Elimination/destructuring is projection
- Proof of conjunction yields proof of each conjunct

### Polymorphic Sum Type

- Two one-argument constructors
- Can represent logical *or* of two other propositions
- A value holds a proof of first, or proof of second
- Elimination for *or* is by *case analysis*

<!-- FUNCTION TYPES -->

### Functions in Predicate Logic

#### Partial vs Total Functions

<!-- RECURSIVE TYPES -->

## Recursive Data and Functions

### Motivating Example

Nested Dolls

#### Constructors (introduction rules)

#### Destructors (elimination rules)

#### Evaluation of recursive functions

#### Termination

#### Structural recursion (Lean verifies automatically)

#### Generative recursion (you prove termination)

### Fundamental Recursive Types

#### Natural Numbers

- Data type
- A Zoo of Functions (eliminators)

#### Lists

- One step beyond natural numbers
- Constructors
- Eliminators

#### Trees

- One step beyond lists
- Constructors
- Eliminators

<!-- RECURSIVE TYPES AND FUNCTIONS -->

## Representing Propositions as Types with Terms as Proofs)

- Represent proposition as types.
- Interpret terms (values) as proofs.
- If such a type has a value, it has a proof, and is "true".
- If such a type has no terms (is uninhabited), it's false.

### Represent False by The Empty Type

No proofs means false.

### True: Unit Type

Has exactly one constant term. No other parameter value 
needed to construct this term. It's always there. There
is always a proof of True.

### Define a proof of NOT P to be a proof of P -> False

Given a proposition, P, you need to show that it has 
no proofs. To show this, show that *if P has a proof*
then so does False.  But that's impossible, so P must
have no proofs; P is false; and NOT P must be true.

The crucial idea here is that if P has no proofs, you
can define a function from *any* proof of P to a proof
of False *by cases*, one for each proof of P. But there
are none, so there are no cases to consider, and so the
conclusion follows. Indeed we define NOT P == P -> False.

### Represent (And P Q) as the Polymorphic Product Type

- One two-argument constructor
- Can represent logic *and* of two other propositions
- Value can represent a proof of such a proposition
- Elimination/destructuring is projection
- Proof of conjunction yields proof of each conjunct

### Represent (Or P Q) as the Polymorphic Sum Type

- Two one-argument constructors
- Can represent logical *or* of two other propositions
- A value holds a proof of first, or proof of second
- Elimination for *or* is by *case analysis*

### Represent P => Q (implication) as P -> Q (function)

### Lots of Exercises (Ch 16)

- How to represent bi-implication
- How to represent exclusive or
- All the axioms and identities of propositional logic
- Fun examples involving bread, spread, and filling (etc)

<!-- EXCLUDED MIDDLE -->
## Excluded Middle and Classical Reasoning (18)


<!-- PREDICATES AND PREDICATE LOGIC -->

## Predicates and Predicate Logic

### Parameterized Propositions

- Families of propositions, one for each argument
- Prop: the type of propositions in Lean
- Example: isEven as n%2=0
- predicates of multiple arguments
- Equality as a predicate of two arguments
- Examples

<!-- QUANTIFIERS: Introduction and Elimination -->

- All
- Exists
- Mixed

<!-- SET THEORY -->

<!-- INDUCTION -->