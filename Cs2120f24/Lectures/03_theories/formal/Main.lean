import Cs2120f24.Lectures.«03_theories».formal.domain

namespace cs2120f24

-- DOMAIN

-- give names to some terms of type Nat
def zero := Nat.zero
def one' := Nat.succ Nat.zero
def one := Nat.succ Nat.zero
def two := Nat.succ one


-- evaluate some application expressions using pred and poof
#eval pred zero
#eval pred one
#eval pred two
-- Lean provides usual notation for natural numbers
#eval pred 2
#eval pred 3
#eval pred 4

-- what function is poor computing?
-- what is the main point of this example?
#eval poof 0
#eval poof 1
#eval poof 2
#eval poof 3
#eval poof 4
#eval poof 5

-- inc (short for increment) is just another name for succ
#eval inc 0   -- expect 1
#eval inc 1   -- expect 2

-- dec (short for decrement) is defined the same as pred
#eval dec 5

-- add
#eval add 0 5
#eval add 5 0
#eval add 3 7

-- mul
#eval mul 5 0
#eval mul 0 5
#eval mul 5 3

-- eq_zero
#eval eq_zero 0
#eval eq_zero 1
#eval eq_zero 10

-- eq
#eval eq 0 0
#eval eq 0 1
#eval eq 1 0
#eval eq 1 1
#eval eq 3 2
#eval eq 2 3
#eval eq 10 10

-- le (≤)
#eval le 0 0
#eval le 0 2
#eval le 1 0
#eval le 2 0
#eval le 3 3
#eval le 3 4
#eval le 4 3


--
