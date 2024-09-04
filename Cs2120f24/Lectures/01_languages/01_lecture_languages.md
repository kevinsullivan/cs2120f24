1. Languages
2. 
   1. Elements  
      1. Syntax: Symbols and symbolic expressions
      2. Semantic domains: things that symbols/expressions refer to  
      3. Interpretations: associate symbols and expressions with meanings (semantics)  
      4. Moods  
         1) Declarative (indicative) – statement asserting what **is** the case  
         2) Conditional –statement asserting what **is** **if** a particular condition holds
         3) Optative – statement defining a state that **should be** made to prevail  
         4) Imperative – expresses a **command** to carry out a certain action  
         5) Exclamatory – an expression of a strong **emotional** state of affairs  
         6) Subjunctive – expresses uncertainty or **counterfactual**
         7) Interrogative – asks a **question**  
   2. Purposes of Language  
      1. Human Communication  
      2. Sound Reasoning (George Boole)  
      3. Automated reasoning / computation  
   3. Natural vs Formal Languages  
      1. Natural (ordinary spoken, written, signed human languages):
         1) human communication easy  
         2) rigorous expression, reasoning more problematical
         3) ambiguous and imprecise: shoes must be worn, dogs must be carried  
         4) generally not computable (but what about LLMs?)  
      2. Formal (logic, mathematics, programming languages)  
         1) human expression, communication hard
         2) rigorous reasoning is mechanical  
         3) Programming, specification and verification  
   4. Formal Languages  
      1. Imperative  
      2. Declarative  
3. Formal Languages  
   1. Imperative  
      1. Step by step procedure to solve a problem
      2. States, commands, and effects
      3. Example: Python program for square root using Newton’s method  
   2. Declarative  
      1. Common features  
         1) Syntax and Semantics
         2) Domains and Interpretations  
         3) Models: Validity, Satisfiability, Unsatisfiability  
         4) Expressiveness vs Solvability  
      2. Expressiveness Against Efficiency  
4. Declarative Formal Languages  
   1. Quality Tradeoffs  
      1. Expressiveness  
      2. Computational complexity  
         1) Decidability of validity of arbitrary expressions  
         2) Tractability of such a computation  
   2. Case Study: Propositional Logic  
      1. You already know it’s syntax and semantics: Boolean expressions  
      2. Syntax:
         1) variables stand for propositions (e.g., P, Q, R)  
         2) different symbols (/\\, \\/, \~) for same concepts as Python’s &&, ||, \!  
         3) Same syntax for building expressions (e.g., P /\\ Q \\/ R, same as P && Q || R)
         4) Same semantics
            1) semantic domain of single variable is Boolean: { true, false }  
            2) Evaluation of bigger expressions is (modulo details) as in Python  
         5) But now, interesting problems\! Given any propositional logic expression, *exp*  
            1) SAT: does at least one *interpretation* make *exp* evaluate to true?  
            2) Valid: does *exp* evaluate to true under all possible interpretations?
            3) Unsat: are there *no* interpretations that make *exp* evaluate to true?  
         6) Examples: analyze each for being SAT, unsat, valid.
            1) P /\\ \~P  
            2) P \\/ \~P  
            3) P /\\ Q \-\> P (uses the *implies* connective–logical expression builder)  
            4) P \\/ Q \-\> P  
            5) P \\/ Q
