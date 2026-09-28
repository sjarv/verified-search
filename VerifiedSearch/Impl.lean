import Mathlib

/- The window we're using is [lo, hi), exclusive of the higher value.

shrinking left is hi := mid
empty is lo ≥ hi
hi starts at a.size
mid = (lo + hi)/2
-/



/- Without sortedness, this single inteference fails. If target < a[mid], since
a[mid] ≤ a[j] for all j ≥ mid by sortedness, we can conclude that target < a[j] for all
j ≥ mid, and thus target ≠ a[j] for all j ≥ mid.-/
