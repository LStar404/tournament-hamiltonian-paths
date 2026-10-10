import TournamentHamiltonian.ShortWeightedConvolution
import TournamentHamiltonian.PairedPermanentRestoration

/-! Uniform score absorption of the square-root Gaussian comparison error. -/
namespace TournamentHamiltonian

theorem score_error_young {n : ℕ} (hn : 0 < n) (tau K : ℝ) (htau : 0 ≤ tau) :
    K * Real.sqrt (tau / n) ≤ tau / 2 + K ^ 2 / (2 * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let x := Real.sqrt (tau / n)
  have hx : (n : ℝ) * x ^ 2 = tau := by dsimp [x]; rw [Real.sq_sqrt (div_nonneg htau hn0.le)]; field_simp
  have hx2 : ((n : ℝ) * x) ^ 2 = n * tau := by
    calc
      _ = (n : ℝ) * (n * x ^ 2) := by ring
      _ = _ := by rw [hx]
  apply (mul_le_mul_iff_right₀ hn0).mp
  have heq : (n : ℝ) * (tau / 2 + K ^ 2 / (2 * n)) = tau * n / 2 + K ^ 2 / 2 := by field_simp
  rw [heq]
  change n * (K * x) ≤ tau * n / 2 + K ^ 2 / 2
  nlinarith [sq_nonneg ((n : ℝ) * x - K)]

noncomputable def scoreAbsorptionExponent (K : ℝ) : ℝ := K ^ 2 / 2 + K
noncomputable def scoreAbsorptionConstant (K : ℝ) : ℝ :=
  scoreAbsorptionExponent K * Real.exp (scoreAbsorptionExponent K)

theorem exp_div_le_one_add_constant {n : ℕ} (hn : 1 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    Real.exp (c / n) ≤ 1 + (c * Real.exp c) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := exp_sub_one_le_self_mul_exp (c / n)
  have h2 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_self hc hn1))
    (div_nonneg hc hn0.le)
  have heq : c / (n : ℝ) * Real.exp c = (c * Real.exp c) / n := by ring
  rw [heq] at h2
  linarith

theorem score_error_exp_le {n : ℕ} (hn : 1 ≤ n) (tau K : ℝ) (htau : 0 ≤ tau) (hK : 0 ≤ K) :
    Real.exp (-tau + K * Real.sqrt (tau / n) + K / n) ≤
      Real.exp (-tau / 2) * (1 + scoreAbsorptionConstant K / n) := by
  have hy := score_error_young (show 0 < n by omega) tau K htau
  have hc : 0 ≤ scoreAbsorptionExponent K := by unfold scoreAbsorptionExponent; positivity
  have hexp := Real.exp_le_exp.mpr
    (show -tau + K * Real.sqrt (tau / n) + K / n ≤ -tau / 2 + scoreAbsorptionExponent K / n by
      unfold scoreAbsorptionExponent
      have heq : (K ^ 2 / 2 + K) / (n : ℝ) = K ^ 2 / (2 * n) + K / n := by ring
      rw [heq]
      linarith)
  rw [Real.exp_add (-tau / 2) (scoreAbsorptionExponent K / n)] at hexp
  apply hexp.trans
  exact mul_le_mul_of_nonneg_left (exp_div_le_one_add_constant hn _ hc) (Real.exp_nonneg _)

theorem score_error_exp_le_one_add {n : ℕ} (hn : 1 ≤ n) (tau K : ℝ) (htau : 0 ≤ tau) (hK : 0 ≤ K) :
    Real.exp (-tau + K * Real.sqrt (tau / n) + K / n) ≤ 1 + scoreAbsorptionConstant K / n := by
  have h := score_error_exp_le hn tau K htau hK
  have hc : 0 ≤ scoreAbsorptionConstant K := by unfold scoreAbsorptionConstant scoreAbsorptionExponent; positivity
  have he : Real.exp (-tau / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 1 + scoreAbsorptionConstant K / n))

theorem score_error_exp_moment_le {n : ℕ} (hn : 1 ≤ n) (tau K : ℝ) (htau : 0 ≤ tau) (hK : 0 ≤ K) :
    (tau + 1) * Real.exp (-tau + K * Real.sqrt (tau / n) + K / n) ≤
      3 * Real.exp (scoreAbsorptionExponent K) := by
  have h := score_error_exp_le hn tau K htau hK
  have hc : 0 ≤ scoreAbsorptionExponent K := by unfold scoreAbsorptionExponent; positivity
  have hy := Real.mul_exp_neg_le_exp_neg_one (tau / 2)
  have hexp : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have he0 : Real.exp (-tau / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have heq : -(tau / 2) = -tau / 2 := by ring
  rw [heq] at hy
  have hmoment : (tau + 1) * Real.exp (-tau / 2) ≤ 3 := by nlinarith
  have hcdiv : Real.exp (scoreAbsorptionExponent K / n) ≤ Real.exp (scoreAbsorptionExponent K) :=
    Real.exp_le_exp.mpr (div_le_self hc (by exact_mod_cast hn))
  have hyoung := Real.exp_le_exp.mpr
    (show -tau + K * Real.sqrt (tau / n) + K / n ≤ -tau / 2 + scoreAbsorptionExponent K / n by
      have hh := score_error_young (show 0 < n by omega) tau K htau
      unfold scoreAbsorptionExponent
      have hid : (K ^ 2 / 2 + K) / (n : ℝ) = K ^ 2 / (2 * n) + K / n := by ring
      rw [hid]
      linarith)
  rw [Real.exp_add (-tau / 2) (scoreAbsorptionExponent K / n)] at hyoung
  calc
    _ ≤ (tau + 1) * (Real.exp (-tau / 2) * Real.exp (scoreAbsorptionExponent K / n)) :=
      mul_le_mul_of_nonneg_left hyoung (by linarith)
    _ ≤ (tau + 1) * Real.exp (-tau / 2) * Real.exp (scoreAbsorptionExponent K) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hcdiv (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hmoment (Real.exp_nonneg _)

end TournamentHamiltonian
