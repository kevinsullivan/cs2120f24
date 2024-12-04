import Mathlib.Data.Rel

/-!
# Properties of Binary Relations
-/

def isEmptyRel {α β : Type} : Rel α β → Prop :=
  fun (r : Rel α β) => ¬∃ (x : α) (y : β), r x y

def isCompleteRel {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y, r x y

def isTotalRel  {α β : Type} : Rel α β → Prop :=
  fun r => ∀ (x : α), ∃ (y : β), r x y

def isSurjectiveRel {α β : Type} : Rel α β → Prop :=
  fun r => ∀ (y : β), ∃ (x : α), r x y

def isSingleValuedRel {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y z, r x y → r x z → y = z

def isInjectiveRel  {α β : Type} : Rel α β → Prop :=
  fun r => ∀ x y z, r x z → r y z → x = y

def isFunctionalRel {α β : Type} : Rel α β → Prop :=
  isSingleValuedRel

def isFunction {α β : Type} : Rel α β → Prop :=
  isFunctionalRel

def isInjective {α β : Type} : Rel α β → Prop :=
  fun r => isFunction r ∧ isInjectiveRel r

def isSurjective {α β : Type} : Rel α β → Prop :=
  fun r => isFunction r ∧ isSurjectiveRel r

def isOneToOne {α β : Type} : Rel α β → Prop :=
  isInjective

def isOnto {α β : Type} : Rel α β → Prop :=
  isSurjective

def isBijective {α β : Type} : Rel α β → Prop :=
  fun r => isInjective r ∧ isSurjective r

def isManyToOne {α β : Type} : Rel α β → Prop :=
  fun r => ¬isInjective r

def isOneToMany {α β : Type} : Rel α β → Prop :=
  fun r => ¬isFunction r ∧ isInjectiveRel r

def isManyToMany {α β : Type} : Rel α β → Prop :=
  fun r => ¬isFunction r ∧ ¬isInjectiveRel r

def isReflexive {α β : Type} : Rel α α → Prop :=
  fun r => ∀ (a : α), r a a

def isSymmetric {α β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b → r b a

def isTransitive {α β : Type} : Rel α α → Prop :=
  fun r =>  ∀ (a b c : α), r a b → r b c → r a c

def isEquivalence {α  β : Type} : Rel α α → Prop :=
  fun r => (@isReflexive α β r) ∧
           (@isSymmetric  α β r) ∧
           (@isTransitive α β r)

def isAsymmetric {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b → ¬r b a

def isAntisymmetric {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b → r b a → a = b

def isStronglyConnected {α  β : Type} : Rel α α → Prop :=
  fun r => ∀ (a b : α), r a b ∨ r b a

def isPartialOrder {α  β : Type} : Rel α α → Prop :=
  fun r =>
    @isReflexive α β r ∧
    @isAntisymmetric α β r ∧
    @isTransitive α β r

def isTotalOrder {α  β : Type} : Rel α α → Prop :=
  fun r =>
    @isPartialOrder α β r ∧
    @isStronglyConnected α β r

def isLinearOrder {α  β : Type} := @isTotalOrder α β

def isWellOrdering  {α  β : Type} : Rel α α → Prop :=
  fun r =>
    ∀ (s : Set α),
      s ≠ ∅ →
      -- think of r as "less than", this this means ...
      -- there's some m ∈ s with no n ∈ s "less than" it
      ∃ m, (m ∈ s ∧ ¬∃ n ∈ s, r n m)
