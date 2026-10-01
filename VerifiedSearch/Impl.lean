import Mathlib
/-! Binary search implementation. The window we're using is [lo, hi).-/

/-- Searches for target within [lo, hi) and returns an index of target if it is
present, or none of it is absent. -/
def binarySearchGo (a : Array Nat) (target : Nat) (lo hi : Nat) : Option Nat :=
  if lo ≥ hi then
    none
  else
    let mid : Nat := (lo + hi)/2
    match a[mid]? with
    | none => none
    | some v =>
      if v = target then
        some mid
      else if v < target  then
      -- a[mid]<target, so we drop into the right branch
        binarySearchGo a target (mid+1) hi
      else
      -- target < a[mid], so we drop into the left branch
        binarySearchGo a target lo mid
termination_by hi - lo

/-- Binary search on a sorted array. Returns none if target is absent, or the
occurrence of an index of target if it is present. -/
def binarySearch (a : Array Nat) (target : Nat) : Option Nat:=
  binarySearchGo a target 0 a.size

#guard binarySearch #[1, 3, 5, 7, 9] 5 == some 2
#guard binarySearch #[1, 3, 5, 7, 9] 1 == some 0
#guard binarySearch #[1, 3, 5, 7, 9] 9 == some 4
#guard binarySearch #[1, 3, 5, 7, 9] 4 == none
#guard binarySearch (#[] : Array Nat) 3 == none
#guard binarySearch #[42] 42 == some 0
#guard binarySearch #[42] 7 == none

#guard binarySearch #[1, 5, 5, 5, 9] 5 == some 2
-- Spec will permit any of the three possible indices

#guard binarySearch #[3, 5, 7] 1 == none
#guard binarySearch #[3, 5, 7] 9 == none
