import Sorting.Implementation

def Sorted (input output : List Nat) : Prop :=
  output.Pairwise (· ≤ ·) ∧ output.Perm input

theorem sort_ascending : forall xs : List Nat,
    (sort xs).Pairwise (· ≤ ·) := by
  grind
#check sort_ascending -- output below
-- sort_ascending (xs : List Nat) :
--   List.Pairwise (fun x1 x2 => x1 ≤ x2) (sort xs)

theorem sort_permutation : forall xs : List Nat,
    (sort xs).Perm xs := by
  grind
#check sort_permutation
-- sort_permutation (xs : List Nat) : (sort xs).Perm xs

theorem sort_correct : forall xs : List Nat,
    Sorted xs (sort xs) := by
  intros xs
  constructor
  · exact sort_ascending xs
  · exact sort_permutation xs
#check sort_correct 
-- sort_correct (xs : List Nat) : Sorted xs (sort xs)
#print axioms sort_correct 
-- 'sort_correct' does not depend on any axioms

#eval sort [2,3,3,1] -- [1,2,3]
#eval (sort [2,3,3,1]).Perm [2,3,3,1] -- not a perm
