namespace cs2120f24.natArithmetic.domain

/-!
# Domain: natural number arithmetic

## The Nat Type

We use Lean's definition of the Nat type.
-/

/-!
## Operations

### Unary Operations
-/

def id : Nat → Nat
| n => n

def inc : Nat → Nat
| n => n + 1       -- Nat.succ n

def pred : Nat → Nat
| 0 => 0        -- Nat.zero
| n' + 1 => n'  -- Nat.succ n'

def dec : Nat → Nat := pred     -- read this carefully and understand it

def fac : Nat → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fac n'


/-!
### Binary Operations
-/

def add : Nat → Nat → Nat
| n, 0 => n
| n, (m' + 1) => (add n m') + 1

def sub : Nat → Nat → Nat
| 0, _ => 0
| n, 0 => n
| (n' + 1), (m' + 1) => sub n' m'

def mul : Nat → Nat → Nat
| _, 0 => 0
| n, (m' + 1) => add n (mul n m')

def exp : Nat → Nat → Nat
| _, 0 => 1
| n, (m' + 1) => n * exp n m'

/-!
## Relations

### Unary Relations
-/

def isEq0 : Nat → Bool
| 0 => true
| _ => false

def isEven : Nat → Bool
| 0 => true
| 1 => false
| n'' + 2 => isEven n''

def isOdd : Nat → Bool
| n => !(isEven n)


/-!
### Binary Relations
-/

def eq : Nat → Nat → Bool
| 0, 0 => true
| 0, _ => false
| _, 0 => false
| (n' + 1), (m' + 1) => eq n' m'

def le : Nat → Nat → Bool
| 0, _ => true
| (_ + 1), 0 => false
| (n' + 1), (m' + 1) => le n' m'

def gt : Nat → Nat → Bool
| n, m => ¬ le n m

def lt : Nat → Nat → Bool
| n, m => le n m && !(eq n m)

def ge : Nat → Nat → Bool
| n, m => gt n m || eq n m

end cs2120f24.natArithmetic.domain
