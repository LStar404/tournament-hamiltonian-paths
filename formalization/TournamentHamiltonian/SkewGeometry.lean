import TournamentHamiltonian.SkewOperatorNorm
import Mathlib.Algebra.Order.Star.Real

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

/-- The full centered kernel used before deletion and scaling in Section 4.2. -/
noncomputable def shiftedSkewKernel {n : ℕ} (T : Tournament n) : Matrix (Fin n) (Fin n) ℝ :=
  ((1 : ℝ) / (n - 1 : ℝ)) • (signMatrix T - 1)

theorem shiftedSkewKernel_gram {n : ℕ} (T : Tournament n) :
    (shiftedSkewKernel T).transpose * shiftedSkewKernel T =
      ((1 : ℝ) / (n - 1 : ℝ) ^ 2) •
        ((signMatrix T).transpose * signMatrix T + 1) := by
  unfold shiftedSkewKernel
  rw [Matrix.transpose_smul, smul_mul_assoc, Matrix.mul_smul, smul_smul]
  have hcoeff : ((1 : ℝ) / (n - 1 : ℝ)) * (1 / (n - 1 : ℝ)) =
      1 / (n - 1 : ℝ) ^ 2 := by simp [pow_two]
  rw [hcoeff]
  congr 1
  rw [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, mul_sub, mul_sub,
    mul_one, one_mul, one_mul, signMatrix_transpose]
  abel

theorem skew_inner_zero {n : ℕ} (T : Tournament n) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signMatrix T) x) = 0 := by
  rw [Matrix.inner_toEuclideanCLM]
  exact skew_quadratic_zero _ (signMatrix_skew T) _

theorem shiftedSkewKernel_action_sq {n : ℕ} (T : Tournament n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (shiftedSkewKernel T) x‖ ^ 2 =
      (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signMatrix T) x‖ ^ 2 + ‖x‖ ^ 2) /
        (n - 1 : ℝ) ^ 2 := by
  have hinner : inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signMatrix T) x) x = 0 := by
    rw [real_inner_comm, skew_inner_zero]
  simp only [shiftedSkewKernel, map_smul, map_sub, map_one,
    smul_apply, sub_apply,
    one_apply_eq_self, norm_smul, mul_pow,
    norm_sub_sq_real, hinner, mul_zero, sub_zero, Real.norm_eq_abs, sq_abs]
  rw [div_pow]
  simp [div_eq_mul_inv, mul_comm]

theorem signMatrix_opNorm_sq_le {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ‖signMatrix T‖ ^ 2 ≤ (n : ℝ) * (n - 1) / 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := normalizedRealSkewOpNorm_sq_le T hn
  unfold normalizedRealSkewOpNorm at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow, div_pow] at h
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (n : ℝ))
  field_simp at hmul
  nlinarith

noncomputable def shiftedSkewNormBudget (n : ℕ) : ℝ :=
  ((n : ℝ) * (n - 1) / 2 + 1) / (n - 1 : ℝ) ^ 2

theorem shiftedSkewKernel_action_sq_le {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (shiftedSkewKernel T) x‖ ^ 2 ≤
      shiftedSkewNormBudget n * ‖x‖ ^ 2 := by
  rw [shiftedSkewKernel_action_sq]
  have hnorm : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signMatrix T) x‖ ≤
      ‖signMatrix T‖ * ‖x‖ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
      ContinuousLinearMap.le_opNorm
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (signMatrix T)) x
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow] at hsquare
  have hbudget := mul_le_mul_of_nonneg_right (signMatrix_opNorm_sq_le T hn) (sq_nonneg ‖x‖)
  calc
    _ ≤ (((n : ℝ) * (n - 1) / 2) * ‖x‖ ^ 2 + ‖x‖ ^ 2) / (n - 1 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by unfold shiftedSkewNormBudget; ring

theorem shiftedSkewNormBudget_nonneg (n : ℕ) : 0 ≤ shiftedSkewNormBudget n := by
  by_cases hn : n = 0
  · subst n; norm_num [shiftedSkewNormBudget]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    unfold shiftedSkewNormBudget
    positivity

set_option maxHeartbeats 1000000 in
theorem shiftedSkewKernel_opNorm_le {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ‖shiftedSkewKernel T‖ ≤ Real.sqrt (shiftedSkewNormBudget n) := by
  rw [Matrix.cstar_norm_def (n := Fin n) (𝕜 := ℝ)]
  apply ContinuousLinearMap.opNorm_le_bound
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (shiftedSkewKernel T)) (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (shiftedSkewNormBudget_nonneg n)]
  exact shiftedSkewKernel_action_sq_le T hn x

theorem shiftedSkewKernel_opNorm_sq_le {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    ‖shiftedSkewKernel T‖ ^ 2 ≤ shiftedSkewNormBudget n := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (shiftedSkewKernel_opNorm_le T hn) 2
  rwa [Real.sq_sqrt (shiftedSkewNormBudget_nonneg n)] at h

theorem shiftedSkewNormBudget_gap (n : ℕ) (hn : 1 < n) :
    1 - shiftedSkewNormBudget n = (n : ℝ) * (n - 3) / (2 * (n - 1 : ℝ) ^ 2) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold shiftedSkewNormBudget
  field_simp [hne]
  ring

theorem shiftedSkewNormBudget_lt_one (n : ℕ) (hn : 4 ≤ n) : shiftedSkewNormBudget n < 1 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hn3 : 0 < (n : ℝ) - 3 := by linarith
  have hgap := shiftedSkewNormBudget_gap n (by omega)
  have hpos : 0 < (n : ℝ) * (n - 3) / (2 * (n - 1 : ℝ) ^ 2) := by positivity
  linarith

theorem shiftedSkewKernel_opNorm_lt_one {n : ℕ} (T : Tournament n) (hn : 4 ≤ n) :
    ‖shiftedSkewKernel T‖ < 1 := by
  have h := shiftedSkewKernel_opNorm_sq_le T (by omega)
  have hcap := shiftedSkewNormBudget_lt_one n hn
  nlinarith [norm_nonneg (shiftedSkewKernel T)]

theorem shiftedSkewKernel_entry_sq {n : ℕ} (T : Tournament n) (i j : Fin n) :
    shiftedSkewKernel T i j ^ 2 = 1 / (n - 1 : ℝ) ^ 2 := by
  by_cases hij : i = j
  · subst j
    simp [shiftedSkewKernel, signMatrix]
  · simp only [shiftedSkewKernel, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
      Matrix.one_apply_ne hij, sub_zero, mul_pow, signMatrix_sq, ite_eq_right hij]
    simp

theorem shiftedSkewKernel_row_sq {n : ℕ} (T : Tournament n) (i : Fin n) :
    (∑ j, shiftedSkewKernel T i j ^ 2) = (n : ℝ) / (n - 1 : ℝ) ^ 2 := by
  simp [shiftedSkewKernel_entry_sq, div_eq_mul_inv]

theorem shiftedSkewKernel_column_sq {n : ℕ} (T : Tournament n) (j : Fin n) :
    (∑ i, shiftedSkewKernel T i j ^ 2) = (n : ℝ) / (n - 1 : ℝ) ^ 2 := by
  simp [shiftedSkewKernel_entry_sq, div_eq_mul_inv]

theorem shiftedSkewKernel_row_sum {n : ℕ} (T : Tournament n) (i : Fin n) :
    (∑ j, shiftedSkewKernel T i j) = (score T i - 1) / (n - 1 : ℝ) := by
  simp only [shiftedSkewKernel, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [score, Matrix.one_apply, div_eq_mul_inv, mul_comm]

theorem shiftedSkewKernel_column_sum {n : ℕ} (T : Tournament n) (j : Fin n) :
    (∑ i, shiftedSkewKernel T i j) = (-score T j - 1) / (n - 1 : ℝ) := by
  have hcol : (∑ i, signMatrix T i j) = -score T j := by
    unfold score
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact signMatrix_skew T i j
  simp only [shiftedSkewKernel, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hcol]
  simp [Matrix.one_apply, div_eq_mul_inv, mul_comm]

theorem shiftedSkewKernel_row_sum_sq {n : ℕ} (T : Tournament n) :
    (∑ i, (∑ j, shiftedSkewKernel T i j) ^ 2) =
      ((∑ i, score T i ^ 2) + n) / (n - 1 : ℝ) ^ 2 := by
  simp only [shiftedSkewKernel_row_sum, div_pow, ← Finset.sum_div]
  congr 1
  have hp : ∀ i : Fin n, (score T i - 1) ^ 2 = score T i ^ 2 - 2 * score T i + 1 := by
    intro i; ring
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    score_sum_zero, mul_zero, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem shiftedSkewKernel_column_sum_sq {n : ℕ} (T : Tournament n) :
    (∑ j, (∑ i, shiftedSkewKernel T i j) ^ 2) =
      ((∑ i, score T i ^ 2) + n) / (n - 1 : ℝ) ^ 2 := by
  simp only [shiftedSkewKernel_column_sum, div_pow, ← Finset.sum_div]
  congr 1
  have hp : ∀ i : Fin n, (-score T i - 1) ^ 2 = score T i ^ 2 + 2 * score T i + 1 := by
    intro i; ring
  simp only [hp, Finset.sum_add_distrib, ← Finset.mul_sum,
    score_sum_zero, mul_zero, add_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem signMatrix_gram_trace {n : ℕ} (T : Tournament n) :
    ((signMatrix T).transpose * signMatrix T).trace = (n : ℝ) * (n - 1) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two]
  rw [Finset.sum_comm]
  exact signMatrix_total_sq T

theorem shiftedSkewKernel_gram_difference {n : ℕ} (T : Tournament n) (hn : 1 < n) :
    (shiftedSkewKernel T).transpose * shiftedSkewKernel T -
        ((1 : ℝ) / (n : ℝ) ^ 2) • ((signMatrix T).transpose * signMatrix T) =
      ((2 * (n : ℝ) - 1) / ((n : ℝ) ^ 2 * (n - 1 : ℝ) ^ 2)) •
        ((signMatrix T).transpose * signMatrix T) +
      ((1 : ℝ) / (n - 1 : ℝ) ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hcoeff : (1 : ℝ) / (n - 1 : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2 =
      (2 * (n : ℝ) - 1) / ((n : ℝ) ^ 2 * (n - 1 : ℝ) ^ 2) := by
    field_simp [hn0, hn1]
    ring
  rw [shiftedSkewKernel_gram, ← hcoeff, smul_add, sub_smul]
  abel

theorem shiftedSkewKernel_gram_difference_posSemidef {n : ℕ} (T : Tournament n)
    (hn : 1 < n) :
    ((shiftedSkewKernel T).transpose * shiftedSkewKernel T -
      ((1 : ℝ) / (n : ℝ) ^ 2) • ((signMatrix T).transpose * signMatrix T)).PosSemidef := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hGram : ((signMatrix T).transpose * signMatrix T).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (signMatrix T)
  rw [shiftedSkewKernel_gram_difference T hn]
  apply Matrix.PosSemidef.add
  · apply hGram.smul
    have hc : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    positivity
  · exact Matrix.PosSemidef.one.smul (by positivity)

theorem shiftedSkewKernel_gram_difference_trace {n : ℕ} (T : Tournament n) (hn : 1 < n) :
    ((shiftedSkewKernel T).transpose * shiftedSkewKernel T -
      ((1 : ℝ) / (n : ℝ) ^ 2) • ((signMatrix T).transpose * signMatrix T)).trace =
      (2 * (n : ℝ) - 1) / ((n : ℝ) * (n - 1)) + n / (n - 1 : ℝ) ^ 2 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  rw [shiftedSkewKernel_gram_difference T hn, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one, signMatrix_gram_trace]
  simp only [Fintype.card_fin, smul_eq_mul]
  field_simp [hn0, hn1]

end TournamentHamiltonian
