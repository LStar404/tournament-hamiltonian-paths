import TournamentHamiltonian.PreconditioningMarginals

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def massNormalizedMatrix (X : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  ((Fintype.card ι : ℝ) / matrixEntryMass X) • X

omit [Fintype ι] in
theorem matrixRowError_smul (X : Matrix ι κ ℝ) (c : ℝ) (i : ι) :
    matrixRowError (c • X) i = c * matrixRowError X i + (c - 1) := by
  simp only [matrixRowError, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem matrixColumnError_smul (X : Matrix ι ι ℝ) (c : ℝ) (j : ι) :
    matrixColumnError (c • X) j = c * matrixColumnError X j + (c - 1) := by
  simp only [matrixColumnError, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem massNormalizedMatrix_mass (X : Matrix ι κ ℝ) (hM : matrixEntryMass X ≠ 0) :
    matrixEntryMass (massNormalizedMatrix X) = Fintype.card ι :=
  matrixEntryMass_normalize X _ hM

theorem normalized_row_error_sum_sq (X : Matrix ι κ ℝ) (hM : matrixEntryMass X ≠ 0) :
    (∑ i, matrixRowError (massNormalizedMatrix X) i ^ 2) =
      ((Fintype.card ι : ℝ) / matrixEntryMass X) ^ 2 * (∑ i, matrixRowError X i ^ 2) -
        (Fintype.card ι : ℝ) * ((matrixEntryMass X - Fintype.card ι) / matrixEntryMass X) ^ 2 := by
  simp only [massNormalizedMatrix, matrixRowError_smul]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [mul_pow, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcross : (∑ i, 2 * ((Fintype.card ι : ℝ) / matrixEntryMass X * matrixRowError X i) *
      ((Fintype.card ι : ℝ) / matrixEntryMass X - 1)) =
      2 * ((Fintype.card ι : ℝ) / matrixEntryMass X) *
        ((Fintype.card ι : ℝ) / matrixEntryMass X - 1) * (matrixEntryMass X - Fintype.card ι) := by
    rw [← matrixRowError_sum X, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross]
  field_simp
  ring

theorem normalized_column_error_sum_sq (X : Matrix ι ι ℝ) (hM : matrixEntryMass X ≠ 0) :
    (∑ j, matrixColumnError (massNormalizedMatrix X) j ^ 2) =
      ((Fintype.card ι : ℝ) / matrixEntryMass X) ^ 2 * (∑ j, matrixColumnError X j ^ 2) -
        (Fintype.card ι : ℝ) * ((matrixEntryMass X - Fintype.card ι) / matrixEntryMass X) ^ 2 := by
  have hm : matrixEntryMass X.transpose = matrixEntryMass X := by
    unfold matrixEntryMass
    exact Finset.sum_comm
  have h := normalized_row_error_sum_sq X.transpose (by rw [hm]; exact hM)
  simpa only [massNormalizedMatrix, hm, matrixRowError, matrixColumnError,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] using h

theorem mass_normalization_factor_bounds (X : Matrix ι κ ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) :
    0 ≤ (Fintype.card ι : ℝ) / matrixEntryMass X ∧
      (Fintype.card ι : ℝ) / matrixEntryMass X ≤ 2 := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hMp : 0 < matrixEntryMass X := by linarith
  refine ⟨div_nonneg hnR.le hMp.le, ?_⟩
  apply (div_le_iff₀ hMp).mpr
  linarith

theorem normalized_row_error_sum_sq_le (X : Matrix ι κ ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) :
    (∑ i, matrixRowError (massNormalizedMatrix X) i ^ 2) ≤
      4 * (∑ i, matrixRowError X i ^ 2) := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hMp : 0 < matrixEntryMass X := by linarith
  rw [normalized_row_error_sum_sq X hMp.ne']
  have hf := mass_normalization_factor_bounds X hn hM
  have hs := pow_le_pow_left₀ hf.1 hf.2 2
  have hsum : 0 ≤ ∑ i, matrixRowError X i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hs hsum,
    mul_nonneg hnR.le (sq_nonneg ((matrixEntryMass X - Fintype.card ι) / matrixEntryMass X))]

theorem normalized_column_error_sum_sq_le (X : Matrix ι ι ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) :
    (∑ j, matrixColumnError (massNormalizedMatrix X) j ^ 2) ≤
      4 * (∑ j, matrixColumnError X j ^ 2) := by
  have hm : matrixEntryMass X.transpose = matrixEntryMass X := by
    unfold matrixEntryMass
    exact Finset.sum_comm
  have h := normalized_row_error_sum_sq_le X.transpose hn (by rw [hm]; exact hM)
  simpa only [massNormalizedMatrix, hm, matrixRowError, matrixColumnError,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] using h

theorem mass_normalization_factor_error (X : Matrix ι κ ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) :
    |(Fintype.card ι : ℝ) / matrixEntryMass X - 1| ≤
      2 * |matrixEntryMass X - Fintype.card ι| / Fintype.card ι := by
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hMp : 0 < matrixEntryMass X := by linarith
  have he : (Fintype.card ι : ℝ) / matrixEntryMass X - 1 =
      -(matrixEntryMass X - Fintype.card ι) / matrixEntryMass X := by
    field_simp
    ring
  rw [he, abs_div, abs_neg, abs_of_pos hMp]
  apply (div_le_div_iff₀ hMp hnR).mpr
  have h := mul_le_mul_of_nonneg_left hM (abs_nonneg (matrixEntryMass X - Fintype.card ι))
  nlinarith

theorem normalized_row_error_abs_le (X : Matrix ι κ ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) (i : ι) :
    |matrixRowError (massNormalizedMatrix X) i| ≤
      2 * |matrixRowError X i| + 2 * |matrixEntryMass X - Fintype.card ι| / Fintype.card ι := by
  rw [massNormalizedMatrix, matrixRowError_smul]
  have hf := mass_normalization_factor_bounds X hn hM
  calc
    _ ≤ |(Fintype.card ι : ℝ) / matrixEntryMass X * matrixRowError X i| +
        |(Fintype.card ι : ℝ) / matrixEntryMass X - 1| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hf.1]
      exact add_le_add (mul_le_mul_of_nonneg_right hf.2 (abs_nonneg _))
        (mass_normalization_factor_error X hn hM)

theorem normalized_column_error_abs_le (X : Matrix ι ι ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) (j : ι) :
    |matrixColumnError (massNormalizedMatrix X) j| ≤
      2 * |matrixColumnError X j| + 2 * |matrixEntryMass X - Fintype.card ι| / Fintype.card ι := by
  rw [massNormalizedMatrix, matrixColumnError_smul]
  have hf := mass_normalization_factor_bounds X hn hM
  calc
    _ ≤ |(Fintype.card ι : ℝ) / matrixEntryMass X * matrixColumnError X j| +
        |(Fintype.card ι : ℝ) / matrixEntryMass X - 1| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hf.1]
      exact add_le_add (mul_le_mul_of_nonneg_right hf.2 (abs_nonneg _))
        (mass_normalization_factor_error X hn hM)

theorem normalized_entry_bounds (X : Matrix ι κ ℝ) (K : ℝ)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X)
    (hX : ∀ i j, 0 ≤ X i j ∧ X i j ≤ K / Fintype.card ι) (i : ι) (j : κ) :
    0 ≤ massNormalizedMatrix X i j ∧
      massNormalizedMatrix X i j ≤ 2 * K / Fintype.card ι := by
  have hf := mass_normalization_factor_bounds X hn hM
  change 0 ≤ ((Fintype.card ι : ℝ) / matrixEntryMass X) * X i j ∧ _
  refine ⟨mul_nonneg hf.1 (hX i j).1, ?_⟩
  change ((Fintype.card ι : ℝ) / matrixEntryMass X) * X i j ≤ _
  calc
    _ ≤ 2 * X i j := mul_le_mul_of_nonneg_right hf.2 (hX i j).1
    _ ≤ 2 * (K / Fintype.card ι) := mul_le_mul_of_nonneg_left (hX i j).2 (by norm_num)
    _ = _ := by ring

theorem massNormalizedMatrix_transpose_of_card_eq (X : Matrix ι κ ℝ)
    (hcard : Fintype.card κ = Fintype.card ι) :
    (massNormalizedMatrix X).transpose = massNormalizedMatrix X.transpose := by
  have hm : matrixEntryMass X.transpose = matrixEntryMass X := by
    unfold matrixEntryMass
    exact Finset.sum_comm
  ext i j
  simp only [massNormalizedMatrix, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, hcard, hm]

theorem normalized_rect_column_error_sum_sq_le (X : Matrix ι κ ℝ)
    (hcard : Fintype.card κ = Fintype.card ι)
    (hn : 0 < Fintype.card ι) (hM : (Fintype.card ι : ℝ) / 2 ≤ matrixEntryMass X) :
    (∑ j, matrixColumnError (massNormalizedMatrix X) j ^ 2) ≤
      4 * (∑ j, matrixColumnError X j ^ 2) := by
  have hm : matrixEntryMass X.transpose = matrixEntryMass X := by
    unfold matrixEntryMass
    exact Finset.sum_comm
  have h := normalized_row_error_sum_sq_le X.transpose (by rw [hcard]; exact hn)
    (by rw [hcard, hm]; exact hM)
  rw [← massNormalizedMatrix_transpose_of_card_eq X hcard] at h
  simpa only [matrixRowError, matrixColumnError, Matrix.transpose_apply] using h

end TournamentHamiltonian
