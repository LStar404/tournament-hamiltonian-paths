import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Matrix.Permanent
import TournamentHamiltonian.Packing

/-! Definitions matching the manuscript's finite objects and final claim.
`MainBound` is a proposition to prove, not an axiom or a proved theorem. -/

namespace TournamentHamiltonian

/-- A loopless orientation of every pair of distinct labelled vertices. -/
def IsTournament {n : ℕ} (A : Fin n → Fin n → Bool) : Prop :=
  (∀ i, A i i = false) ∧ (∀ i j, i ≠ j → A i j = !A j i)

abbrev Tournament (n : ℕ) := {A : Fin n → Fin n → Bool // IsTournament A}

noncomputable instance (n : ℕ) : Fintype (Tournament n) := Fintype.ofFinite _

/-- A permutation lists a directed Hamiltonian path in order. Reversal is
not quotiented out. At order zero this predicate is vacuous. -/
def IsHamiltonian {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → T.val (σ i) (σ j) = true

noncomputable def pathCount {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact (Finset.univ.filter (IsHamiltonian T)).card

/-- Maximum over all labelled tournaments; labelling does not affect counts. -/
noncomputable def maxPaths (n : ℕ) : ℕ := by
  classical
  exact Finset.univ.sup (pathCount (n := n))

noncomputable def meanPaths (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) / 2 ^ (n - 1)

noncomputable def lowerConstant : ℝ := Real.cosh 1 / Real.cos 1

/-- The actual user-requested main theorem, quantified uniformly in order.
The `n ≥ 2` clause keeps the normalization in its intended domain. -/
def MainBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    (lowerConstant - K / n) * meanPaths n ≤ (maxPaths n : ℝ) ∧
    (maxPaths n : ℝ) ≤ (upperConstant + K / n) * meanPaths n

theorem pathCount_le_factorial {n : ℕ} (T : Tournament n) :
    pathCount T ≤ Nat.factorial n := by
  classical
  unfold pathCount
  calc
    (Finset.univ.filter (IsHamiltonian T)).card ≤
        (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Nat.factorial n := by simp [Fintype.card_perm]

theorem pathCount_le_maxPaths {n : ℕ} (T : Tournament n) :
    pathCount T ≤ maxPaths n := by
  classical
  exact Finset.le_sup (Finset.mem_univ T)

theorem maxPaths_le_factorial (n : ℕ) : maxPaths n ≤ Nat.factorial n := by
  classical
  exact Finset.sup_le (fun T _ => pathCount_le_factorial T)

/-- Sign-matrix convention: an arc from row to column has sign +1. -/
def signMatrix {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else if T.val i j then 1 else -1

def adjacency {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if T.val i j then 1 else 0

theorem twice_adjacency {n : ℕ} (T : Tournament n) (i j : Fin n) :
    2 * adjacency T i j = 1 - (if i = j then 1 else 0) + signMatrix T i j := by
  by_cases h : i = j
  · subst j
    simp [adjacency, signMatrix, T.property.1]
  · cases he : T.val i j <;> norm_num [adjacency, signMatrix, h, he]

theorem signMatrix_skew {n : ℕ} (T : Tournament n) (i j : Fin n) :
    signMatrix T i j = -signMatrix T j i := by
  by_cases h : i = j
  · subst j; simp [signMatrix]
  · have hrev := T.property.2 i j h
    cases he : T.val j i <;> simp_all [signMatrix, Ne.symm h]

noncomputable def score {n : ℕ} (T : Tournament n) (i : Fin n) : ℝ :=
  ∑ j, signMatrix T i j

theorem score_sum_zero {n : ℕ} (T : Tournament n) : ∑ i, score T i = 0 := by
  unfold score
  have h : (∑ i, ∑ j, signMatrix T i j) = -(∑ i, ∑ j, signMatrix T i j) := by
    calc
      (∑ i, ∑ j, signMatrix T i j) = ∑ j, ∑ i, signMatrix T i j :=
        Finset.sum_comm
      _ = ∑ j, ∑ i, -signMatrix T j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact signMatrix_skew T i j
      _ = -(∑ j, ∑ i, signMatrix T j i) := by simp
  linarith

theorem signMatrix_sq {n : ℕ} (T : Tournament n) (i j : Fin n) :
    signMatrix T i j ^ 2 = if i = j then 0 else 1 := by
  by_cases h : i = j
  · simp [signMatrix, h]
  · cases he : T.val i j <;> simp [signMatrix, h, he]

/-- Squared Frobenius mass, before spectral pairing divides it by two. -/
theorem signMatrix_total_sq {n : ℕ} (T : Tournament n) :
    (∑ i, ∑ j, signMatrix T i j ^ 2) = (n : ℝ) * (n - 1) := by
  simp_rw [signMatrix_sq]
  have hrow : ∀ i : Fin n, (∑ j : Fin n, if i = j then (0 : ℝ) else 1) = n - 1 := by
    intro i
    have heq : (∑ j : Fin n, if i = j then (0 : ℝ) else 1) =
        (∑ j : Fin n, (1 : ℝ)) - ∑ j : Fin n, if i = j then (1 : ℝ) else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j <;> simp [h]
    rw [heq]
    simp
  simp_rw [hrow]
  simp
  ring

end TournamentHamiltonian
