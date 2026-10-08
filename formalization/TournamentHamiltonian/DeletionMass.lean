import TournamentHamiltonian.ScalingIdentities
import TournamentHamiltonian.SkewGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def matrixEntryMass (X : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, X i j

noncomputable def matrixRowError (X : Matrix ι κ ℝ) (i : ι) : ℝ := (∑ j, X i j) - 1

noncomputable def matrixColumnError (X : Matrix ι κ ℝ) (j : κ) : ℝ := (∑ i, X i j) - 1

private theorem sum_compl_eq_sub (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ sᶜ, f i) = (∑ i, f i) - ∑ i ∈ s, f i := by
  have h := Finset.sum_add_sum_compl s f
  linarith

/-- Inclusion-exclusion of actual entry mass for arbitrary different row
and column deletion sets. -/
theorem matrixEntryMass_deleted (X : Matrix ι κ ℝ) (I : Finset ι) (J : Finset κ) :
    matrixEntryMass (X.submatrix (Subtype.val : (Iᶜ : Finset ι) → ι) (Subtype.val : (Jᶜ : Finset κ) → κ)) =
      matrixEntryMass X - (∑ i ∈ I, ∑ j, X i j) -
        (∑ j ∈ J, ∑ i, X i j) + ∑ i ∈ I, ∑ j ∈ J, X i j := by
  let f : ι → κ → ℝ := X
  change (∑ i : (Iᶜ : Finset ι), ∑ j : (Jᶜ : Finset κ), f i j) =
    (∑ i, ∑ j, f i j) - (∑ i ∈ I, ∑ j, f i j) -
      (∑ j ∈ J, ∑ i, f i j) + ∑ i ∈ I, ∑ j ∈ J, f i j
  simp only [Finset.sum_coe_sort]
  simp_rw [sum_compl_eq_sub J]
  rw [Finset.sum_sub_distrib,
    Finset.sum_coe_sort (Iᶜ) (fun i => ∑ j, f i j),
    Finset.sum_coe_sort (Iᶜ) (fun i => ∑ j ∈ J, f i j),
    sum_compl_eq_sub I, sum_compl_eq_sub I]
  have hcol : (∑ i, ∑ j ∈ J, f i j) = ∑ j ∈ J, ∑ i, f i j := Finset.sum_comm
  rw [hcol]
  ring

theorem matrixEntryMass_deleted_errors (X : Matrix ι κ ℝ) (I : Finset ι) (J : Finset κ) :
    matrixEntryMass (X.submatrix (Subtype.val : (Iᶜ : Finset ι) → ι) (Subtype.val : (Jᶜ : Finset κ) → κ)) =
      matrixEntryMass X - I.card - J.card -
        (∑ i ∈ I, matrixRowError X i) - (∑ j ∈ J, matrixColumnError X j) +
        ∑ i ∈ I, ∑ j ∈ J, X i j := by
  rw [matrixEntryMass_deleted]
  simp only [matrixRowError, matrixColumnError, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixEntryMass_smul (X : Matrix ι κ ℝ) (c : ℝ) :
    matrixEntryMass (c • X) = c * matrixEntryMass X := by
  simp [matrixEntryMass, Matrix.smul_apply, Finset.mul_sum]

/-- The exact kappa formula used before true scaling in Section 4.3. -/
theorem normalized_deleted_mass {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (hI : I.card = t) (hJ : J.card = t)
    (ht : t < n) (hmass : matrixEntryMass X = n) :
    matrixEntryMass (((n : ℝ) / (n - t : ℝ)) •
      X.submatrix (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) - (n - t : ℝ) =
      ((n : ℝ) / (n - t : ℝ)) *
        (-(∑ i ∈ I, matrixRowError X i) - (∑ j ∈ J, matrixColumnError X j) +
          (∑ i ∈ I, ∑ j ∈ J, X i j) - (t : ℝ) ^ 2 / n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have htR : (t : ℝ) < n := by exact_mod_cast ht
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hnt : (n : ℝ) - t ≠ 0 := by linarith
  rw [matrixEntryMass_smul, matrixEntryMass_deleted_errors, hmass, hI, hJ]
  field_simp [hn0, hnt]
  ring

theorem normalized_deleted_row_error {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (ht : t < n) (i : (Iᶜ : Finset (Fin n))) :
    matrixRowError (((n : ℝ) / (n - t : ℝ)) •
      X.submatrix (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n) (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) i =
      ((n : ℝ) / (n - t : ℝ)) *
        (matrixRowError X i + (t : ℝ) / n - ∑ j ∈ J, X i j) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt ht)
  have htR : (t : ℝ) < n := by exact_mod_cast ht
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hnt : (n : ℝ) - t ≠ 0 := by linarith
  let f : Fin n → Fin n → ℝ := X
  change (∑ j : (Jᶜ : Finset (Fin n)), ((n : ℝ) / (n - t : ℝ)) * f i j) - 1 =
    ((n : ℝ) / (n - t : ℝ)) *
      ((∑ j, f i j) - 1 + (t : ℝ) / n - ∑ j ∈ J, f i j)
  rw [← Finset.mul_sum, Finset.sum_coe_sort, sum_compl_eq_sub]
  field_simp [hn0, hnt]
  ring

theorem normalized_deleted_column_error {n t : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (I J : Finset (Fin n)) (ht : t < n) (j : (Jᶜ : Finset (Fin n))) :
    matrixColumnError (((n : ℝ) / (n - t : ℝ)) •
      X.submatrix (Subtype.val : (Iᶜ : Finset (Fin n)) → Fin n)
        (Subtype.val : (Jᶜ : Finset (Fin n)) → Fin n)) j =
      ((n : ℝ) / (n - t : ℝ)) *
        (matrixColumnError X j + (t : ℝ) / n - ∑ i ∈ I, X i j) := by
  simpa only [matrixRowError, matrixColumnError, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply] using
      normalized_deleted_row_error X.transpose J I ht j

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixEntryMass_normalize (X : Matrix ι κ ℝ) (a : ℝ)
    (hmass : matrixEntryMass X ≠ 0) :
    matrixEntryMass ((a / matrixEntryMass X) • X) = a := by
  rw [matrixEntryMass_smul]
  exact div_mul_cancel₀ a hmass

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixRowError_sum (X : Matrix ι κ ℝ) :
    (∑ i, matrixRowError X i) = matrixEntryMass X - Fintype.card ι := by
  simp [matrixRowError, matrixEntryMass, Finset.sum_sub_distrib]

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixColumnError_sum (X : Matrix ι κ ℝ) :
    (∑ j, matrixColumnError X j) = matrixEntryMass X - Fintype.card κ := by
  simp only [matrixColumnError, matrixEntryMass, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm]

theorem normalized_row_errors_sum_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hmass : matrixEntryMass X = n) : (∑ i, matrixRowError X i) = 0 := by
  rw [matrixRowError_sum, Fintype.card_fin, hmass, sub_self]

theorem normalized_column_errors_sum_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hmass : matrixEntryMass X = n) : (∑ j, matrixColumnError X j) = 0 := by
  rw [matrixColumnError_sum, Fintype.card_fin, hmass, sub_self]

/-- The actual normalized tournament adjacency used in Section 4.3. -/
noncomputable def tournamentDensity {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  ((2 : ℝ) / (n - 1 : ℝ)) • adjacency T

theorem tournamentDensity_eq_shiftedSkew {n : ℕ} (T : Tournament n) :
    tournamentDensity T =
      ((1 : ℝ) / (n - 1 : ℝ)) • Matrix.of (fun _ _ => 1) + shiftedSkewKernel T := by
  ext i j
  simp only [tournamentDensity, shiftedSkewKernel, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
  have h := twice_adjacency T i j
  calc
    _ = ((1 : ℝ) / (n - 1 : ℝ)) * (2 * adjacency T i j) := by ring
    _ = _ := by rw [h]; ring

theorem tournamentDensity_row_error {n : ℕ} (T : Tournament n) (hn : 1 < n) (i : Fin n) :
    matrixRowError (tournamentDensity T) i = score T i / (n - 1 : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [tournamentDensity_eq_shiftedSkew]
  simp only [matrixRowError, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mul_one, Finset.sum_add_distrib, shiftedSkewKernel_row_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hne]
  ring

theorem tournamentDensity_column_error {n : ℕ} (T : Tournament n) (hn : 1 < n) (j : Fin n) :
    matrixColumnError (tournamentDensity T) j = -score T j / (n - 1 : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [tournamentDensity_eq_shiftedSkew]
  simp only [matrixColumnError, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mul_one, Finset.sum_add_distrib, shiftedSkewKernel_column_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hne]
  ring

theorem tournamentDensity_mass {n : ℕ} (T : Tournament n) (hn : 1 < n) :
    matrixEntryMass (tournamentDensity T) = n := by
  have h : (∑ i, matrixRowError (tournamentDensity T) i) = 0 := by
    simp only [tournamentDensity_row_error T hn, ← Finset.sum_div, score_sum_zero, zero_div]
  rw [matrixRowError_sum, Fintype.card_fin] at h
  exact sub_eq_zero.mp h

end TournamentHamiltonian
