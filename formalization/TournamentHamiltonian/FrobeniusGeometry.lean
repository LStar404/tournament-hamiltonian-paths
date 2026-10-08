import TournamentHamiltonian.CenteredPreconditioning

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrix_flat_euclidean_norm (X : Matrix ι κ ℝ) :
    ‖(WithLp.toLp 2 (fun ij : ι × κ => X ij.1 ij.2) : EuclideanSpace ℝ (ι × κ))‖ =
      realFrobeniusNorm X := by
  rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_eq]
  simp [realFrobeniusNorm, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]

omit [DecidableEq ι] [DecidableEq κ] in
theorem realFrobeniusNorm_add_le (X Y : Matrix ι κ ℝ) :
    realFrobeniusNorm (X + Y) ≤ realFrobeniusNorm X + realFrobeniusNorm Y := by
  let x : EuclideanSpace ℝ (ι × κ) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)
  let y : EuclideanSpace ℝ (ι × κ) := WithLp.toLp 2 (fun ij => Y ij.1 ij.2)
  have hxy : (WithLp.toLp 2 (fun ij : ι × κ => (X + Y) ij.1 ij.2) : EuclideanSpace ℝ (ι × κ)) = x + y := by
    ext ij
    rfl
  rw [← matrix_flat_euclidean_norm (X + Y), hxy, ← matrix_flat_euclidean_norm X,
    ← matrix_flat_euclidean_norm Y]
  exact norm_add_le x y

omit [DecidableEq ι] [DecidableEq κ] in
theorem realFrobeniusNorm_smul (X : Matrix ι κ ℝ) (c : ℝ) :
    realFrobeniusNorm (c • X) = |c| * realFrobeniusNorm X := by
  let x : EuclideanSpace ℝ (ι × κ) := WithLp.toLp 2 (fun ij => X ij.1 ij.2)
  have hc : (WithLp.toLp 2 (fun ij : ι × κ => (c • X) ij.1 ij.2) : EuclideanSpace ℝ (ι × κ)) = c • x := by
    ext ij
    rfl
  rw [← matrix_flat_euclidean_norm (c • X), hc, norm_smul, Real.norm_eq_abs,
    ← matrix_flat_euclidean_norm X]

omit [DecidableEq ι] [DecidableEq κ] in
theorem realFrobeniusNorm_submatrix_le (X : Matrix ι κ ℝ) (R : Finset ι) (C : Finset κ) :
    realFrobeniusNorm (X.submatrix (Subtype.val : R → ι) (Subtype.val : C → κ)) ≤
      realFrobeniusNorm X := by
  apply (sq_le_sq₀ (realFrobeniusNorm_nonneg _) (realFrobeniusNorm_nonneg _)).mp
  rw [realFrobeniusNorm_sq, realFrobeniusNorm_sq]
  calc
    _ ≤ ∑ i : R, ∑ j : κ, X i j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      change (∑ j : C, X i j ^ 2) ≤ _
      rw [Finset.sum_coe_sort C (fun j => X i j ^ 2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = ∑ i ∈ R, ∑ j, X i j ^ 2 := Finset.sum_coe_sort R (fun i => ∑ j, X i j ^ 2)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [DecidableEq κ] in
theorem realFrobeniusNorm_mul_le_opNorm_left (X : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) :
    realFrobeniusNorm (A * X) ≤ ‖A‖ * realFrobeniusNorm X := by
  calc
    _ = realFrobeniusNorm ((A * X).transpose) := (realFrobeniusNorm_transpose _).symm
    _ = realFrobeniusNorm (X.transpose * A.transpose) := by rw [Matrix.transpose_mul]
    _ ≤ realFrobeniusNorm X.transpose * ‖A.transpose‖ := realFrobeniusNorm_mul_le_opNorm_right _ _
    _ = _ := by
      rw [realFrobeniusNorm_transpose]
      have ht : ‖A.transpose‖ = ‖A‖ := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A
      rw [ht, mul_comm]

theorem centeredMatrix_frobenius_le (X : Matrix ι κ ℝ)
    (hp : 0 < Fintype.card ι) (hq : 0 < Fintype.card κ) :
    realFrobeniusNorm (centeringProjection ι * X * centeringProjection κ) ≤
      realFrobeniusNorm X := by
  have hl := centeringProjection_opNorm_le_one hp
  have hr := centeringProjection_opNorm_le_one hq
  calc
    _ ≤ realFrobeniusNorm (centeringProjection ι * X) * ‖centeringProjection κ‖ :=
      realFrobeniusNorm_mul_le_opNorm_right _ _
    _ ≤ realFrobeniusNorm (centeringProjection ι * X) :=
      mul_le_of_le_one_right (realFrobeniusNorm_nonneg _) hr
    _ ≤ ‖centeringProjection ι‖ * realFrobeniusNorm X := realFrobeniusNorm_mul_le_opNorm_left _ _
    _ ≤ _ := mul_le_of_le_one_left (realFrobeniusNorm_nonneg _) hl

theorem shiftedSkewKernel_frobenius_sq {n : ℕ} (T : Tournament n) :
    realFrobeniusNorm (shiftedSkewKernel T) ^ 2 = (n : ℝ) ^ 2 / (n - 1 : ℝ) ^ 2 := by
  rw [realFrobeniusNorm_sq]
  simp only [shiftedSkewKernel_entry_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem shiftedSkewKernel_frobenius_le_two {n : ℕ} (T : Tournament n) (hn : 1 < n) :
    realFrobeniusNorm (shiftedSkewKernel T) ≤ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hn1 : 0 < (n - 1 : ℝ) := by linarith
  apply (sq_le_sq₀ (realFrobeniusNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp
  rw [shiftedSkewKernel_frobenius_sq]
  apply (div_le_iff₀ (sq_pos_of_pos hn1)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ 3 * (n : ℝ) - 2 by linarith)]

noncomputable def preconditioningCenteredDisplacementBudget {n t : ℕ} (T : Tournament n)
    (a0 : ℝ) (I J : Finset (Fin n)) : ℝ :=
  2 * |preconditioningDeletionEta (t := t) T I J - 1| +
    16 * |preconditioningDeletionEta (t := t) T I J| / (1 - a0) ^ 2 *
      Real.sqrt (scoreVariance T / n)

theorem normalizedDeletedPreconditioned_centered_frobenius_displacement {n t : ℕ} (T : Tournament n)
    (hn : 1 < n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0) :
    realFrobeniusNorm (centeringProjection (Iᶜ : Finset (Fin n)) *
      normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
        centeringProjection (Jᶜ : Finset (Fin n)) - centeredDeletedSkewKernel T I J) ≤
      preconditioningCenteredDisplacementBudget (t := t) T a0 I J := by
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hq : 0 < Fintype.card (Jᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hJ]
    omega
  let Z := centeredDeletedSkewKernel T I J
  let F := centeringProjection (Iᶜ : Finset (Fin n)) *
    (preconditionedDensityDifference T).submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n) *
        centeringProjection (Jᶜ : Finset (Fin n))
  let eta := preconditioningDeletionEta (t := t) T I J
  have hZ : realFrobeniusNorm Z ≤ 2 :=
    (centeredMatrix_frobenius_le (deletedShiftedSkewKernel T I J) hp hq).trans
      ((realFrobeniusNorm_submatrix_le (shiftedSkewKernel T) Iᶜ Jᶜ).trans
        (shiftedSkewKernel_frobenius_le_two T hn))
  have hF : realFrobeniusNorm F ≤ 16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) :=
    (centeredMatrix_frobenius_le _ hp hq).trans
      ((realFrobeniusNorm_submatrix_le (preconditionedDensityDifference T) Iᶜ Jᶜ).trans
        (preconditionedDensityDifference_frobenius_bound T hn a0 h0 h1 ha))
  rw [normalizedDeletedPreconditioned_centered_eq T I J hI ht hM hX]
  change realFrobeniusNorm (eta • (Z + F) - Z) ≤ _
  have he : eta • (Z + F) - Z = (eta - 1) • Z + eta • F := by module
  rw [he]
  calc
    _ ≤ realFrobeniusNorm ((eta - 1) • Z) + realFrobeniusNorm (eta • F) := realFrobeniusNorm_add_le _ _
    _ = |eta - 1| * realFrobeniusNorm Z + |eta| * realFrobeniusNorm F := by
      rw [realFrobeniusNorm_smul, realFrobeniusNorm_smul]
    _ ≤ |eta - 1| * 2 + |eta| * (16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) :=
      add_le_add (mul_le_mul_of_nonneg_left hZ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hF (abs_nonneg _))
    _ = _ := by unfold preconditioningCenteredDisplacementBudget; dsimp [eta]; ring

end TournamentHamiltonian
