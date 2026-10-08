import TournamentHamiltonian.LocalScalingCapacity
import TournamentHamiltonian.NormalizationBounds

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def massRestoredLocalPotentials (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    (ι ⊕ ι) → ℝ := fun k => z k + (1 / 2) * Real.log (Fintype.card ι / matrixEntryMass X)

omit [DecidableEq ι] in
theorem massRestoredLocalPotentials_capacity (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    localScalingCapacity (massRestoredLocalPotentials X z) =
      localScalingCapacity z + Fintype.card ι * Real.log (Fintype.card ι / matrixEntryMass X) := by
  simp only [massRestoredLocalPotentials, localScalingCapacity, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem massRestoredLocalPotentials_gauge (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    localGaugeFunctional (massRestoredLocalPotentials X z) = localGaugeFunctional z := by
  simp only [massRestoredLocalPotentials, localGaugeFunctional, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem massRestoredLocalPotentials_scaledMatrix (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (hM : 0 < matrixEntryMass X) (z : (ι ⊕ ι) → ℝ) :
    localScaledMatrix X (massRestoredLocalPotentials X z) =
      localScaledMatrix (massNormalizedMatrix X) z := by
  have hpR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  ext i j
  have harg : massRestoredLocalPotentials X z (Sum.inl i) +
      massRestoredLocalPotentials X z (Sum.inr j) =
      (z (Sum.inl i) + z (Sum.inr j)) + Real.log (Fintype.card ι / matrixEntryMass X) := by
    dsimp [massRestoredLocalPotentials]
    ring
  simp only [localScaledMatrix, harg, Real.exp_add,
    Real.exp_log (div_pos hpR hM), massNormalizedMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

theorem localScaledMatrix_permanent_restoration (X : Matrix ι ι ℝ) (z : (ι ⊕ ι) → ℝ) :
    X.permanent = Real.exp (-localScalingCapacity z) * (localScaledMatrix X z).permanent := by
  rw [localScaledMatrix_eq_exp_scaling]
  exact permanent_exp_restoration X (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j))

theorem normalized_local_scaling_permanent_restoration (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hM : 0 < matrixEntryMass X) (z : (ι ⊕ ι) → ℝ) :
    X.permanent = Real.exp (-(localScalingCapacity z +
      Fintype.card ι * Real.log (Fintype.card ι / matrixEntryMass X))) *
        (localScaledMatrix (massNormalizedMatrix X) z).permanent := by
  rw [← massRestoredLocalPotentials_capacity, ← massRestoredLocalPotentials_scaledMatrix X hp hM]
  exact localScaledMatrix_permanent_restoration X (massRestoredLocalPotentials X z)

theorem matrix_permanent_nonneg_of_nonneg (X : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j) :
    0 ≤ X.permanent := by
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => hX (σ i) i))

omit [DecidableEq ι] in
theorem massNormalizedMatrix_nonnegative (X : Matrix ι ι ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hM : 0 < matrixEntryMass X) (i j : ι) : 0 ≤ massNormalizedMatrix X i j := by
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hM.le) (hX i j)

omit [DecidableEq ι] in
theorem normalized_local_scaling_capacity_lower (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hM : 0 < matrixEntryMass X) (z : (ι ⊕ ι) → ℝ)
    (hz : 0 ≤ localScalingCapacity z) :
    -localScalingCapacity (massRestoredLocalPotentials X z) ≤ matrixEntryMass X - Fintype.card ι := by
  have hpR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hM hpR)) hpR.le
  have hl : Real.log (Fintype.card ι / matrixEntryMass X) =
      -Real.log (matrixEntryMass X / Fintype.card ι) := by
    rw [Real.log_div hpR.ne' hM.ne', Real.log_div hM.ne' hpR.ne']
    ring
  rw [massRestoredLocalPotentials_capacity, hl]
  have hc : (Fintype.card ι : ℝ) * (matrixEntryMass X / Fintype.card ι - 1) =
      matrixEntryMass X - Fintype.card ι := by field_simp [hpR.ne']
  rw [hc] at h
  linarith

theorem normalized_local_scaling_permanent_upper (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hX : ∀ i j, 0 ≤ X i j) (hM : 0 < matrixEntryMass X)
    (z : (ι ⊕ ι) → ℝ)
    (hrow : ∀ i, ∑ j, localScaledMatrix (massNormalizedMatrix X) z i j = 1)
    (hcol : ∀ j, ∑ i, localScaledMatrix (massNormalizedMatrix X) z i j = 1) :
    X.permanent ≤ Real.exp (matrixEntryMass X - Fintype.card ι) *
      (localScaledMatrix (massNormalizedMatrix X) z).permanent := by
  have hnormX := massNormalizedMatrix_nonnegative X hX hM
  have hz := localScalingCapacity_nonnegative (massNormalizedMatrix X) hnormX
    (massNormalizedMatrix_mass X hM.ne') z hrow hcol
  have hc := normalized_local_scaling_capacity_lower X hp hM z hz
  rw [localScaledMatrix_permanent_restoration X (massRestoredLocalPotentials X z),
    massRestoredLocalPotentials_scaledMatrix X hp hM]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc)
    (matrix_permanent_nonneg_of_nonneg _ (localScaledMatrix_nonnegative _ hnormX z))

end TournamentHamiltonian
