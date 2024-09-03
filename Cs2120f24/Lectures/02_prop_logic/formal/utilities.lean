/-!
#### Low-level bit vector routines
-/

namespace cs2120f24

/-!
Converting natural number indices to corresponding rows of
truth tables for any given v, a number of variables.
-/

-- rightmost bit in binary representation of given natural number, n
def right_bit (n : Nat) := n%2

-- dividing n by 2 discards rightmost bit in binary representation of n
def shift_right (n : Nat) := n/2

-- convert natural number to corresponding list of bits (nat, 0 or 1)
def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := by sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

/-!
Left pad list of nats with zeros
Todo: Clarify bits vs nats
-/
def list_nat_zero_pad : List Nat → Nat → List Nat
  | l, n => zero_pad_recursive (n - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | n'+1, l => zero_pad_recursive n' (0::l)

/-!
 Make bit list at index "row" zero padded "cols" wide
-/
def mk_bit_row_pad : (row : Nat) → (cols: Nat) → List Nat
| r, c => list_nat_zero_pad (nat_to_bin r) c

/-!
Convert bit to bool
-/
def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

/-!
convert list of bits to list Bools
-/
def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

/-!
Make row'th row of truth table with vars variable columns
-/
def list_bool_from_row_index_and_cols : (row : Nat) → (vars : Nat) → List Bool
| index, cols => bit_list_to_bool_list (mk_bit_row_pad index cols)


/-!
### Generalized Boolean reductions
-/

-- functions to check if bool list has any, resp. all, values true
def reduce_or : List Bool → Bool
| [] => false
| h::t => or h (reduce_or t)

def reduce_and : List Bool → Bool
| [] => true
| h::t => and h (reduce_and t)
