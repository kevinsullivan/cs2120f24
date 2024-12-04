import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation


/-!
# Sets

| Name          | Set Theory Notation   | Set Theory Definition     | Membership Predicate           |
|---------------|-----------------------|---------------------------|--------------------------------|
| Set           | set α                 | axioms of set theory      | (α → Prop)                     |
| member        | x ∈ a                 | membership predicate*     | (a x)                          |
| intersection  | s ∩ t                 | { a | a ∈ s ∧ a ∈ t }     | fun a => (s a) ∧ (t a)         |
| union         | s ∪ t                 | { a | a ∈ s ∨ a ∈ t }     | fun a => (s a) ∨ (t a)         |
| complement    | sᶜ                    | { a | a ∉ s }             | fun a => ¬(s a)                |
| difference    | s \ t                 | { a | a ∈ s ∧ a ∉ t }     | fun a => (s a) ∧ ¬(t a) )      |
| subset        | s ⊆ t                 | ∀ a, a ∈ s → a ∈ t  ...   | fun a => (s a) → (t a)         |
| proper subset | s ⊊ t                 | ... ∧ ∃ w, w ∈ t ∧ w ∉ s  | ... ∧ ∃ w, (t w) ∧ ¬(s w)      |
| product set   | s × t                 | { (a,b) | a ∈ s ∧ b ∈ t } | fun (a, b) => (s a) /\ (t b)   |
| powerset      | 𝒫 s                   | { t | t ⊆ s }             | fun t => ∀ ⦃a : ℕ⦄, t a → s a   |

* for us; but there are other ways of specifying membership, e.g., axiomatically
-/

#reduce Set.inter
#reduce Set.union
#reduce Set.compl
#reduce Set.diff
#reduce @Set.Subset
#reduce Set.prod
#reduce Set.powerset
