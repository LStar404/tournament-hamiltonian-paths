import TournamentHamiltonian.UniformNonprincipalScaling
import TournamentHamiltonian.PreconditionedGaussianComparison

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectangular_unit_marginals_centering (B : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (hr : ∀ i, ∑ j, B i j = 1) (hc : ∀ j, ∑ i, B i j = 1) :
    centeringProjection ι * B * centeringProjection κ = B - rectangularAverageMatrix ι κ := by
  have hmass : matrixEntryMass B = Fintype.card ι := by
    unfold matrixEntryMass
    simp_rw [hr]
    simp
  rw [← rectangularCenteredKernel_eq_centering B e hp hmass]
  ext i j
  simp only [rectangularCenteredKernel, matrixRowError, matrixColumnError, hr, hc,
    sub_self, zero_add, zero_div, sub_zero, Matrix.sub_apply, rectangularAverageMatrix]

theorem rectangularScaling_gaussian_finite_comparison (X : Matrix ι κ ℝ) (e : ι ≃ κ)
    (hp : 0 < Fintype.card ι) (K C eps : ℝ) (x : ι → ℝ) (y : κ → ℝ)
    (hxy : RectangularScalingWitness X e K C (9 / 10) eps x y)
    (hX : ‖centeringProjection ι * X * centeringProjection κ‖ ≤ 9 / 10)
    (hXf : realFrobeniusNorm (centeringProjection ι * X * centeringProjection κ) ≤ 3)
    (hdisp : realFrobeniusNorm (rectangularExpScaling X x y - X) ≤ 1) :
    |Real.log (gramGaussian (rectangularExpScaling X x y - rectangularAverageMatrix ι κ)) -
      Real.log (gramGaussian (centeringProjection ι * X * centeringProjection κ))| ≤
        (1400 / 39) * realFrobeniusNorm (rectangularExpScaling X x y - X) := by
  let B := rectangularExpScaling X x y
  let U := B - rectangularAverageMatrix ι κ
  let V := centeringProjection ι * X * centeringProjection κ
  have hk : 0 < Fintype.card κ := by rw [← Fintype.card_congr e]; exact hp
  have hB := rectangular_unit_marginals_centering B e hp hxy.row_sum hxy.column_sum
  have hd : U - V = centeringProjection ι * (B - X) * centeringProjection κ := by
    dsimp [U, V]
    rw [← hB, Matrix.mul_sub, Matrix.sub_mul]
  have hdf : realFrobeniusNorm (U - V) ≤ realFrobeniusNorm (B - X) := by
    rw [hd]
    exact centeredMatrix_frobenius_le _ hp hk
  have hUf : realFrobeniusNorm U ≤ 4 := by
    have heq : U = (U - V) + V := by abel
    have h := realFrobeniusNorm_add_le (U - V) V
    rw [← heq] at h
    change realFrobeniusNorm (B - X) ≤ 1 at hdisp
    change realFrobeniusNorm V ≤ 3 at hXf
    linarith
  have hUq : ‖U‖ ≤ (19 / 20 : ℝ) := by
    have h := hxy.gap
    norm_num at h
    exact h
  have hVq : ‖V‖ ≤ (19 / 20 : ℝ) := hX.trans (by norm_num)
  have hLip := gramGaussian_log_lipschitz U V (19 / 20) (by norm_num) (by norm_num) hUq hVq
  have hprod := mul_le_mul (show realFrobeniusNorm U + realFrobeniusNorm V ≤ 7 by linarith)
    hdf (realFrobeniusNorm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
  have h := div_le_div_of_nonneg_right hprod
    (by norm_num : (0 : ℝ) ≤ 2 * (1 - (19 / 20 : ℝ) ^ 2))
  exact hLip.trans (h.trans_eq (by ring))

end TournamentHamiltonian
