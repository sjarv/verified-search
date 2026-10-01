import Mathlib

/-! Specification for binary search. This file defines what it means for a
search function to be correct, without reference to the particular search function.
Correctness has two halves, IsSound and IsCorrect.

* IsSound: if f returns an index, the target is actually there; holds for any array,
sorted or not.
* IsComplete: if f returns 'none', the target is actually absent; requires sortedness.

Sortedness itself is defined in two ways, which are equivalent; the 'Fin' version
makes sortedness decidable.
-/

namespace VerifiedSearch

/-- An array is sorted if every earlier index holds a value at most that of
every later index. -/
def Array.SortedPairs (a : Array Nat) : Prop :=
  ∀ i j : Nat, (hi : i < a.size) → (hj : j < a.size) → i ≤ j → a[i] ≤ a[j]

/-- An array is sorted if every index holds a value less than or equal to the value
held at the next immediate index. -/
def Array.SortedAdj (a : Array Nat) : Prop :=
  ∀ i : Nat, (hi : i +1 < a.size) → a[i] ≤ a[i+1]

/- I'll take Array.SortedPairs as my definition of sortedness; when I implement binary
search, I want to use that target < a[mid] to conclude that target isn't in the right
branch, i.e. target ≠ a[j] for all j ≥ mid. Using SortedPairs, I have that
a[mid] ≤ a[j] for all such j, and this chains with target < a[mid] to get
target < a[j] (and thus target ≠ a[j]). -/

/-- Finite version of SortedPairs; we only need to consider naturals ≤ a.size. -/
abbrev Array.SortedPairsFin (a : Array Nat) : Prop :=
  ∀ i j : Fin (a.size), i ≤ j → a[i] ≤ a[j]

example : Decidable (Array.SortedPairsFin a) := by
  exact inferInstance

/-- Both definitions say an array is sorted, and just differ in how the indices are
packaged. -/
lemma Array.sortedPairs_iff_sortedPairsFin (a : Array Nat) :
Array.SortedPairs a ↔ Array.SortedPairsFin a := by
  constructor
  · intro h i j hij;
    have hi : ↑i < a.size := i.isLt
    have hj : ↑j < a.size := j.isLt
    apply h i j hi hj hij
  · intro h i j hi hj hij
    apply h ⟨i, hi⟩ ⟨j, hj⟩ hij

#check decidable_of_iff

/-- Proves that Array.SortedPairs is decidable: given an array a, I can always
answer 'this is sorted (according to Array.SortedPairs)' or not. -/
instance (a : Array Nat) : Decidable (Array.SortedPairs a) := by
  exact decidable_of_iff (Array.SortedPairsFin a) (Array.sortedPairs_iff_sortedPairsFin a).symm

/-- If your search function returns some i, that's a genuine occurrence. Does not require
sortedness. -/
def IsSound (f : Array Nat → Nat → Option Nat) : Prop :=
  ∀ a target, ∀ i : Nat, (f a target = some i) → a[i]? = some target

/-- If your search function returns none on a sorted array, the target does not
occur in the array. -/
def IsComplete (f : Array Nat → Nat → Option Nat) : Prop :=
  ∀ a target, Array.SortedPairs a → (f a target = none → ∀ i : Nat, a[i]? ≠ some target)

def IsCorrectSearch (f : Array Nat → Nat → Option Nat) : Prop := IsSound f ∧ IsComplete f

end VerifiedSearch
