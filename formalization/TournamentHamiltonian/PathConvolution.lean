import TournamentHamiltonian.Hadamard
import TournamentHamiltonian.Orientation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Exact finite interfaces for the manuscript's positive path convolution.

The weighted permutation formula below refers to the original `pathCount`.
The determinant/permanent sum is separately defined; its equality with that
path count is proved in `PathConvolutionGenerating` using cycle cancellation.
-/

namespace TournamentHamiltonian

open scoped Classical

/-- The weight of an ordered vertex permutation. The redundant pair index
keeps both empty and singleton orders free of special indexing conventions. -/
noncomputable def pathWeight {n : ℕ} (T : Tournament n)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∏ p : Fin n × Fin n,
    if p.2.val = p.1.val + 1 then adjacency T (σ p.1) (σ p.2) else 1

theorem pathWeight_eq_indicator {n : ℕ} (T : Tournament n)
    (σ : Equiv.Perm (Fin n)) :
    pathWeight T σ = if IsHamiltonian T σ then 1 else 0 := by
  classical
  by_cases h : IsHamiltonian T σ
  · rw [ite_eq_left h]
    unfold pathWeight
    apply Finset.prod_eq_one
    intro p _
    by_cases hp : p.2.val = p.1.val + 1
    · simp [hp, adjacency, h p.1 p.2 hp]
    · simp [hp]
  · rw [ite_eq_right h]
    obtain ⟨i, j, hij, hA⟩ : ∃ i j : Fin n,
        j.val = i.val + 1 ∧ T.val (σ i) (σ j) ≠ true := by
      simp only [IsHamiltonian, not_forall] at h
      obtain ⟨i, j, hij, hA⟩ := h
      exact ⟨i, j, hij, hA⟩
    unfold pathWeight
    apply Finset.prod_eq_zero (Finset.mem_univ (i, j))
    simp [hij, adjacency, hA]

/-- The actual directed Hamiltonian count is the sum of adjacency weights,
without identifying a permutation with its reversal. -/
theorem pathCount_eq_sum_pathWeight {n : ℕ} (T : Tournament n) :
    (pathCount T : ℝ) = ∑ σ : Equiv.Perm (Fin n), pathWeight T σ := by
  classical
  unfold pathCount
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pathWeight_eq_indicator]
  split_ifs <;> norm_num

theorem pathWeight_eq_consecutive_product {n : ℕ} (T : Tournament (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    pathWeight T σ = ∏ i : Fin n, adjacency T (σ i.castSucc) (σ i.succ) := by
  classical
  rw [pathWeight_eq_indicator]
  by_cases h : IsHamiltonian T σ
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [adjacency, (isHamiltonian_iff_consecutive T σ).mp h i]
  · rw [ite_eq_right h]
    have hh : ¬∀ i : Fin n, T.val (σ i.castSucc) (σ i.succ) = true :=
      fun hh => h ((isHamiltonian_iff_consecutive T σ).mpr hh)
    obtain ⟨i, hi⟩ := not_forall.mp hh
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [adjacency, hi])

theorem pathCount_eq_sum_consecutive_product {n : ℕ} (T : Tournament (n + 1)) :
    (pathCount T : ℝ) = ∑ σ : Equiv.Perm (Fin (n + 1)),
      ∏ i : Fin n, adjacency T (σ i.castSucc) (σ i.succ) := by
  rw [pathCount_eq_sum_pathWeight]
  simp_rw [pathWeight_eq_consecutive_product]

/-- Loop-inclusive complement convention used by Irving--Omar. -/
def complementAdjacency {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun _ _ => 1) - adjacency T

theorem complementAdjacency_eq {n : ℕ} (T : Tournament n) :
    complementAdjacency T = 1 + (adjacency T).transpose := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [complementAdjacency, adjacency, T.property.1]
  · have h := T.property.2 i j hij
    cases hji : T.val j i <;>
      simp [complementAdjacency, adjacency, hij, h, hji]

theorem complementAdjacency_principal_det {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    ((complementAdjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).det =
      (principalWeightMatrix T U).det := by
  rw [complementAdjacency_eq]
  have heq : ((1 : Matrix (Fin n) (Fin n) ℝ) + (adjacency T).transpose).submatrix
      (Subtype.val : U → Fin n) Subtype.val = (principalWeightMatrix T U).transpose := by
    ext i j
    simp only [principalWeightMatrix, Matrix.submatrix_apply, Matrix.transpose_apply,
      Matrix.add_apply, Matrix.one_apply]
    congr 1
    simp only [Subtype.ext_iff, eq_comm]
  rw [heq, Matrix.det_transpose]

theorem adjacency_nonneg {n : ℕ} (T : Tournament n) (i j : Fin n) :
    0 ≤ adjacency T i j := by
  unfold adjacency
  split <;> norm_num

theorem adjacency_principal_permanent_nonneg {n : ℕ} (T : Tournament n)
    (U : Finset (Fin n)) :
    0 ≤ ((adjacency T).submatrix (Subtype.val : U → Fin n) Subtype.val).permanent := by
  unfold Matrix.permanent
  exact Finset.sum_nonneg (fun σ _ =>
    Finset.prod_nonneg (fun i _ => adjacency_nonneg T _ _))

/-- The exact determinant/permanent expression from §2.2. Its identification
with `pathCount` is not assumed in this definition. -/
noncomputable def pathConvolutionSum {n : ℕ} (T : Tournament n) : ℝ :=
  ∑ U : Finset (Fin n), (principalWeightMatrix T U).det *
    ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n)
      Subtype.val).permanent

theorem pathConvolutionSum_nonneg {n : ℕ} (T : Tournament n) :
    0 ≤ pathConvolutionSum T := by
  unfold pathConvolutionSum
  exact Finset.sum_nonneg (fun U _ => mul_nonneg (principal_weight_pos T U).le
    (adjacency_principal_permanent_nonneg T Uᶜ))

theorem principal_weight_le_pathConvolutionSum {n : ℕ} (T : Tournament n) :
    (principalWeightMatrix T Finset.univ).det ≤ pathConvolutionSum T := by
  classical
  have h := Finset.single_le_sum
    (fun U (_ : U ∈ (Finset.univ : Finset (Finset (Fin n)))) =>
      mul_nonneg (principal_weight_pos T U).le
        (adjacency_principal_permanent_nonneg T Uᶜ))
    (Finset.mem_univ (Finset.univ : Finset (Fin n)))
  have : IsEmpty ((Finset.univ : Finset (Fin n))ᶜ : Finset (Fin n)) :=
    ⟨fun i => by simpa using i.property⟩
  rw [Matrix.permanent_isEmpty, mul_one] at h
  exact h

theorem pathConvolutionSum_pos {n : ℕ} (T : Tournament n) :
    0 < pathConvolutionSum T :=
  (principal_weight_pos T Finset.univ).trans_le
    (principal_weight_le_pathConvolutionSum T)

/-- Exact grouping by subset cardinality, before any truncation or estimate. -/
theorem pathConvolutionSum_by_card {n : ℕ} (T : Tournament n) :
    pathConvolutionSum T = ∑ k ∈ Finset.range (n + 1),
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (principalWeightMatrix T U).det *
          ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n)
            Subtype.val).permanent := by
  classical
  have h := Finset.sum_powerset (Finset.univ : Finset (Fin n))
    (fun U => (principalWeightMatrix T U).det *
      ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n)
        Subtype.val).permanent)
  simpa [pathConvolutionSum] using h

section GeneratingIdentity

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The rank-one determinant identity underlying the path generating series.
It holds over any commutative ring whenever the walk denominator is a unit,
so it applies in particular to squarefree nilpotent variable algebras. -/
theorem walk_determinant_identity (A : Matrix ι ι R) (z : ι → R)
    (hunit : IsUnit (1 - Matrix.diagonal z * A).det) :
    (1 + Matrix.diagonal z * (Matrix.of (fun _ _ => 1) - A)).det =
      (1 - Matrix.diagonal z * A).det *
        (1 + ∑ i, ((1 - Matrix.diagonal z * A)⁻¹).mulVec z i) := by
  classical
  let M : Matrix ι ι R := 1 - Matrix.diagonal z * A
  have hrank : Matrix.diagonal z * Matrix.of (fun _ _ => (1 : R)) =
      Matrix.replicateCol Unit z * Matrix.replicateRow Unit (fun _ : ι => (1 : R)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have hnum : 1 + Matrix.diagonal z * (Matrix.of (fun _ _ => 1) - A) =
      M + Matrix.replicateCol Unit z * Matrix.replicateRow Unit (fun _ : ι => (1 : R)) := by
    rw [Matrix.mul_sub, ← hrank]
    dsimp [M]
    abel
  rw [hnum, Matrix.det_add_replicateCol_mul_replicateRow hunit]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Matrix.mulVec, dotProduct, one_mul,
    ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]

end GeneratingIdentity

section GeneratingRatio

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem walk_determinant_ratio (A : Matrix ι ι K) (z : ι → K)
    (hdet : (1 - Matrix.diagonal z * A).det ≠ 0) :
    1 + ∑ i, ((1 - Matrix.diagonal z * A)⁻¹).mulVec z i =
      (1 + Matrix.diagonal z * (Matrix.of (fun _ _ => 1) - A)).det /
        (1 - Matrix.diagonal z * A).det := by
  rw [eq_div_iff hdet]
  exact (mul_comm _ _).trans (walk_determinant_identity A z (isUnit_iff_ne_zero.mpr hdet)).symm

end GeneratingRatio

/-- Specialization to the actual tournament adjacency matrix and its correct
loop-inclusive complement. -/
theorem tournament_walk_determinant_ratio {n : ℕ} (T : Tournament n)
    (z : Fin n → ℝ) (hdet : (1 - Matrix.diagonal z * adjacency T).det ≠ 0) :
    1 + ∑ i, ((1 - Matrix.diagonal z * adjacency T)⁻¹).mulVec z i =
      (1 + Matrix.diagonal z * (1 + (adjacency T).transpose)).det /
        (1 - Matrix.diagonal z * adjacency T).det := by
  have h := walk_determinant_ratio (adjacency T) z hdet
  change 1 + ∑ i, ((1 - Matrix.diagonal z * adjacency T)⁻¹).mulVec z i =
    (1 + Matrix.diagonal z * complementAdjacency T).det /
      (1 - Matrix.diagonal z * adjacency T).det at h
  rw [complementAdjacency_eq] at h
  exact h

end TournamentHamiltonian
