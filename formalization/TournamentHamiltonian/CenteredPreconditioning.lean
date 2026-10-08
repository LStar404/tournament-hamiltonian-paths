import TournamentHamiltonian.PreconditioningNormalization
import TournamentHamiltonian.TournamentGaussianLoss

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem centeringProjection_opNorm_le_one (hp : 0 < Fintype.card ι) :
    ‖centeringProjection ι‖ ≤ 1 :=
  rankOneComplement_opNorm_le_one (flatUnitVector ι) (flatUnitVector_sum_sq ι hp)

theorem centeredMatrix_opNorm_le (X : Matrix ι κ ℝ)
    (hp : 0 < Fintype.card ι) (hq : 0 < Fintype.card κ) :
    ‖centeringProjection ι * X * centeringProjection κ‖ ≤ ‖X‖ := by
  have hl := centeringProjection_opNorm_le_one hp
  have hr := centeringProjection_opNorm_le_one hq
  calc
    _ ≤ ‖centeringProjection ι * X‖ * ‖centeringProjection κ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖centeringProjection ι * X‖ := mul_le_of_le_one_right (norm_nonneg _) hr
    _ ≤ ‖centeringProjection ι‖ * ‖X‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖X‖ := mul_le_of_le_one_left (norm_nonneg _) hl

omit [Fintype κ] [DecidableEq κ] in
theorem centeringProjection_mul_ones (hp : 0 < Fintype.card ι) :
    centeringProjection ι * (Matrix.of (fun (_ : ι) (_ : κ) => (1 : ℝ))) = 0 := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [centeringProjection_eq, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  have he : Matrix.of (fun (_ : ι) (_ : ι) => (1 : ℝ)) *
      Matrix.of (fun (_ : ι) (_ : κ) => (1 : ℝ)) =
      (Fintype.card ι : ℝ) • Matrix.of (fun (_ : ι) (_ : κ) => (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he, smul_smul, inv_mul_cancel₀ hcard, one_smul, sub_self]

noncomputable def preconditioningDeletionEta {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) : ℝ :=
  (n : ℝ) ^ 2 / (matrixEntryMass (preconditionedTournamentDensity T) *
    matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J))

theorem normalizedDeletedPreconditioned_eq {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) (hI : I.card = t) (ht : t < n)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0) :
    normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J =
      preconditioningDeletionEta (t := t) T I J •
        (preconditionedTournamentDensity T).submatrix
          (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n) := by
  have htR : (t : ℝ) < n := by exact_mod_cast ht
  have hm : (n - t : ℝ) ≠ 0 := by linarith
  have hc : (Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) = (n - t : ℝ) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI, Nat.cast_sub ht.le]
  let MX := matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J)
  have hMX : MX ≠ 0 := hX
  ext i j
  change ((Fintype.card (Iᶜ : Finset (Fin n)) : ℝ) / MX) *
    (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J i j) =
      ((n : ℝ) ^ 2 / (matrixEntryMass (preconditionedTournamentDensity T) * MX)) *
        preconditionedTournamentDensity T i j
  rw [hc]
  simp only [scaledDeletedMatrix, normalizedPreconditionedDensity, massNormalizedMatrix,
    Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply, Fintype.card_fin]
  field_simp [hm, hM, hMX]

theorem normalizedDeletedPreconditioned_centered_eq {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) (hI : I.card = t) (ht : t < n)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0) :
    centeringProjection (Iᶜ : Finset (Fin n)) *
      normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
        centeringProjection (Jᶜ : Finset (Fin n)) =
      preconditioningDeletionEta (t := t) T I J •
        (centeredDeletedSkewKernel T I J + centeringProjection (Iᶜ : Finset (Fin n)) *
          (preconditionedDensityDifference T).submatrix
            (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n) *
              centeringProjection (Jᶜ : Finset (Fin n))) := by
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  rw [normalizedDeletedPreconditioned_eq T I J hI ht hM hX, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have he : (preconditionedTournamentDensity T).submatrix
      (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n) =
      ((1 : ℝ) / (n - 1 : ℝ)) • Matrix.of
        (fun (_ : (Iᶜ : Finset (Fin n))) (_ : (Jᶜ : Finset (Fin n))) => (1 : ℝ)) +
        deletedShiftedSkewKernel T I J +
        (preconditionedDensityDifference T).submatrix Subtype.val Subtype.val := by
    have hc := tournamentDensity_eq_shiftedSkew T
    ext i j
    have hij := congrFun (congrFun hc i.val) j.val
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one] at hij
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, mul_one, deletedShiftedSkewKernel, preconditionedDensityDifference, Matrix.sub_apply]
    linarith
  rw [he, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_smul,
    centeringProjection_mul_ones hp, smul_zero, Matrix.zero_mul, zero_add]
  rfl

theorem normalizedDeletedPreconditioned_centered_opNorm_le {n t : ℕ} (T : Tournament n)
    (hn : 4 ≤ n) (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t) (ht : t < n)
    (a0 : ℝ) (h0 : 0 ≤ a0) (h1 : a0 < 1) (ha : ∀ i, |tournamentScorePotential T i| ≤ a0)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0) :
    ‖centeringProjection (Iᶜ : Finset (Fin n)) *
      normalizedDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J *
        centeringProjection (Jᶜ : Finset (Fin n))‖ ≤
      |preconditioningDeletionEta (t := t) T I J| *
        (Real.sqrt (shiftedSkewNormBudget n) +
          16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n)) := by
  have hp : 0 < Fintype.card (Iᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hI]
    omega
  have hq : 0 < Fintype.card (Jᶜ : Finset (Fin n)) := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hJ]
    omega
  have hY : ‖centeredDeletedSkewKernel T I J‖ ≤ Real.sqrt (shiftedSkewNormBudget n) :=
    (centeredMatrix_opNorm_le (deletedShiftedSkewKernel T I J) hp hq).trans
      ((submatrix_opNorm_le (shiftedSkewKernel T) Iᶜ Jᶜ).trans
        (shiftedSkewKernel_opNorm_le T (by omega)))
  have hF : ‖centeringProjection (Iᶜ : Finset (Fin n)) *
      (preconditionedDensityDifference T).submatrix
        (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n) *
          centeringProjection (Jᶜ : Finset (Fin n))‖ ≤
      16 / (1 - a0) ^ 2 * Real.sqrt (scoreVariance T / n) :=
    (centeredMatrix_opNorm_le _ hp hq).trans
      ((submatrix_opNorm_le (preconditionedDensityDifference T) Iᶜ Jᶜ).trans
        (preconditionedDensityDifference_opNorm_bound T (by omega) a0 h0 h1 ha))
  rw [normalizedDeletedPreconditioned_centered_eq T I J hI ht hM hX, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add hY hF)

theorem preconditioningDeletionEta_eq_retained_mass {n t : ℕ} (T : Tournament n)
    (I J : Finset (Fin n)) (ht : t < n)
    (hM : matrixEntryMass (preconditionedTournamentDensity T) ≠ 0)
    (hX : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) ≠ 0) :
    preconditioningDeletionEta (t := t) T I J = (n - t : ℝ) /
      matrixEntryMass ((preconditionedTournamentDensity T).submatrix
        (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htR : (t : ℝ) < n := by exact_mod_cast ht
  have hm : (n - t : ℝ) ≠ 0 := by linarith
  let R := (preconditionedTournamentDensity T).submatrix
    (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)
  have he : matrixEntryMass (scaledDeletedMatrix (t := t) (normalizedPreconditionedDensity T) I J) =
      ((n : ℝ) / (n - t : ℝ)) * ((n : ℝ) / matrixEntryMass (preconditionedTournamentDensity T)) * matrixEntryMass R := by
    rw [scaledDeletedMatrix, matrixEntryMass_smul]
    simp only [normalizedPreconditionedDensity, massNormalizedMatrix, Fintype.card_fin]
    change ((n : ℝ) / (n - t : ℝ)) *
      matrixEntryMass (((n : ℝ) / matrixEntryMass (preconditionedTournamentDensity T)) • R) = _
    rw [matrixEntryMass_smul]
    ring
  have hR : matrixEntryMass R ≠ 0 := by
    intro hzero
    rw [he, hzero, mul_zero] at hX
    exact hX rfl
  change preconditioningDeletionEta (t := t) T I J = (n - t : ℝ) / matrixEntryMass R
  unfold preconditioningDeletionEta
  rw [he]
  field_simp [hn.ne', hm, hM, hR]

end TournamentHamiltonian
