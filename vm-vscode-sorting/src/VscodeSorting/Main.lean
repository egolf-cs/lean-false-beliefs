import Implementation

def Sorted (input output : List Nat) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm input

theorem sort_ascending (xs : List Nat) :
    (sort xs).Pairwise (· ≤ ·) := by
  grind
#check sort_ascending

theorem sort_permutation (xs : List Nat) :
    (sort xs).Perm xs := by
  grind
#check sort_permutation

theorem sort_correct (xs : List Nat) : Sorted xs (sort xs) := by
  constructor
  · exact sort_ascending xs
  · exact sort_permutation xs
#check sort_correct
#print axioms sort_correct
