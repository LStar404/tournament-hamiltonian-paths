import TournamentHamiltonian.LocalScaling
import TournamentHamiltonian.CenteredPreconditioning

open scoped Matrix.Norms.L2Operator

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem averagingMatrix_mul_entry (X : Matrix ι ι ℝ) (i j : ι) :
    (averagingMatrix ι * X) i j = (Fintype.card ι : ℝ)⁻¹ * (∑ k, X k j) := by
  simp only [Matrix.mul_apply, averagingMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mul_one, ← Finset.mul_sum]

omit [DecidableEq ι] in
theorem mul_averagingMatrix_entry (X : Matrix ι ι ℝ) (i j : ι) :
    (X * averagingMatrix ι) i j = (Fintype.card ι : ℝ)⁻¹ * (∑ k, X i k) := by
  simp only [Matrix.mul_apply, averagingMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, mul_one, ← Finset.sum_mul]
  ring

omit [DecidableEq ι] in
theorem averagingMatrix_sandwich_entry (X : Matrix ι ι ℝ) (i j : ι) :
    (averagingMatrix ι * X * averagingMatrix ι) i j =
      ((Fintype.card ι : ℝ)⁻¹) ^ 2 * matrixEntryMass X := by
  rw [mul_averagingMatrix_entry]
  simp_rw [averagingMatrix_mul_entry]
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold matrixEntryMass
  ring

theorem localCenteredKernel_eq_centering (X : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (hmass : matrixEntryMass X = Fintype.card ι) :
    localCenteredKernel X = centeringProjection ι * X * centeringProjection ι := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hPi : centeringProjection ι = 1 - averagingMatrix ι := centeringProjection_eq ι
  rw [hPi]
  have he : (1 - averagingMatrix ι) * X * (1 - averagingMatrix ι) =
      X - averagingMatrix ι * X - X * averagingMatrix ι + averagingMatrix ι * X * averagingMatrix ι := by
    noncomm_ring
  rw [he]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [averagingMatrix_mul_entry, mul_averagingMatrix_entry, averagingMatrix_sandwich_entry, hmass]
  simp only [localCenteredKernel, Matrix.sub_apply, marginalBalancedMatrix, matrixRowError, matrixColumnError,
    averagingMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_one]
  field_simp
  ring

omit [DecidableEq ι] in
theorem localCenteredKernel_density_bound (X : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι)
    (K eps : ℝ) (hX : ∀ i j, |X i j| ≤ K / Fintype.card ι)
    (ha : ∀ i, |matrixRowError X i| ≤ eps) (hb : ∀ j, |matrixColumnError X j| ≤ eps)
    (i j : ι) :
    |localCenteredKernel X i j| ≤ (K + 2 * eps + 1) / Fintype.card ι := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have he : localCenteredKernel X i j = X i j -
      (matrixRowError X i + matrixColumnError X j) / Fintype.card ι - (Fintype.card ι : ℝ)⁻¹ := by
    simp only [localCenteredKernel, marginalBalancedMatrix, averagingMatrix, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_one]
  rw [he]
  have ht1 := abs_add_le (X i j) (-((matrixRowError X i + matrixColumnError X j) / Fintype.card ι))
  have ht2 := abs_add_le (X i j - (matrixRowError X i + matrixColumnError X j) / Fintype.card ι)
    (-((Fintype.card ι : ℝ)⁻¹))
  simp only [← sub_eq_add_neg, abs_neg] at ht1 ht2
  have ht3 := abs_add_le (matrixRowError X i) (matrixColumnError X j)
  have he' : |(matrixRowError X i + matrixColumnError X j) / Fintype.card ι| ≤
      2 * eps / Fintype.card ι := by
    rw [abs_div, abs_of_pos hc]
    exact div_le_div_of_nonneg_right (by linarith [ha i, hb j]) hc.le
  rw [abs_of_pos (inv_pos.mpr hc)] at ht2
  have hsum : K / Fintype.card ι + 2 * eps / Fintype.card ι + (Fintype.card ι : ℝ)⁻¹ =
      (K + 2 * eps + 1) / Fintype.card ι := by simp only [div_eq_mul_inv]; ring
  linarith [hX i j]

end TournamentHamiltonian
