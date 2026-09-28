import Mathlib

/-- An array is sorted if every earlier index holds a value at most that of
every later index. -/
def Array.SortedPairs (a : Array Nat) : Prop :=
  ∀ i j : Nat, (hi : i < a.size) → (hj : j < a.size) → i ≤ j → a[i] ≤ a[j]
