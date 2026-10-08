import TournamentHamiltonian.ScoreAbsorption
import TournamentHamiltonian.PairedPermanentErrorBudget

/-! Uniform absorption of the complete actual retained-mass error together with
the weighted generating-function inflation. No mass-defect terms are discarded. -/
namespace TournamentHamiltonian
open Filter
open scoped Topology

noncomputable def fullScoreAbsorptionExponent (K C D : ℝ) : ℝ :=
  (K + C) ^ 2 / 2 + K + C + D

theorem full_score_exponent_uniform (A K C D : ℝ)
    (_hA : 0 ≤ A) (hK : 0 ≤ K) (_hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ A * Real.log (n : ℝ) →
      -tau + K * pairedPermanentErrorBudget n 0 tau +
        C * (tau / n + Real.sqrt (tau / n) + 1 / n) + D / n ≤
          fullScoreAbsorptionExponent K C D / n := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (((hinv.const_mul K).add (hlog.const_mul (K * A))).add
    ((hlog.const_mul A).sqrt.const_mul K)).add (hinv.const_mul C)
  simp only [mul_zero, Real.sqrt_zero, add_zero] at h
  filter_upwards [h.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℕ)] with n hb hn tau htau htA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  change K * (n : ℝ)⁻¹ + K * A * (Real.log (n : ℝ) / n) +
    K * Real.sqrt (A * (Real.log (n : ℝ) / n)) + C * (n : ℝ)⁻¹ ≤ 1 / 2 at hb
  have hb' : K * (1 + A * Real.log (n : ℝ)) / n +
      K * Real.sqrt ((A * Real.log (n : ℝ)) / n) + C / n ≤ 1 / 2 := by
    have heq : A * (Real.log (n : ℝ) / n) = (A * Real.log (n : ℝ)) / n := by ring
    rw [heq] at hb
    convert hb using 1
    ring
  have hroot := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right htA hn0.le)
  have hr : K * (1 + tau) / n + K * Real.sqrt (tau / n) + C / n ≤ 1 / 2 := by
    have hfrac := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) htA) hK) hn0.le
    have hsqrt := mul_le_mul_of_nonneg_left hroot hK
    exact (add_le_add (add_le_add hfrac hsqrt) (le_refl _)).trans hb'
  have hmul := mul_le_mul_of_nonneg_right hr htau
  have hhigh : K * ((tau + tau ^ 2) / n + tau * Real.sqrt (tau / n)) + C * (tau / n) ≤ tau / 2 := by
    convert hmul using 1 <;> ring
  have hy := score_error_young (show 0 < n by omega) tau (K + C) htau
  calc
    _ = -tau + (K * ((tau + tau ^ 2) / n + tau * Real.sqrt (tau / n)) + C * (tau / n)) +
        (K + C) * Real.sqrt (tau / n) + (K + C + D) / n := by
      unfold pairedPermanentErrorBudget
      norm_num
      ring
    _ ≤ -tau + tau / 2 + (tau / 2 + (K + C) ^ 2 / (2 * n)) + (K + C + D) / n := by
      linarith
    _ = _ := by unfold fullScoreAbsorptionExponent; ring

theorem actual_full_score_factor_uniform (A K C D : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament n,
      (∀ i, |tournamentScorePotential T i| ≤ 1) → scoreVariance T ≤ A * Real.log (n : ℝ) →
      pairedScoreProduct T * Real.exp
        (K * pairedPermanentErrorBudget n 0 (scoreVariance T) +
          C * (scoreVariance T / n + Real.sqrt (scoreVariance T / n) + 1 / n) + D / n) ≤
            1 + (fullScoreAbsorptionExponent K C D * Real.exp (fullScoreAbsorptionExponent K C D)) / n := by
  filter_upwards [full_score_exponent_uniform A K C D hA hK hC,
    eventually_ge_atTop (1 : ℕ)] with n he hn T ha hvar
  have hτ := scoreVariance_nonneg T
  have hs := pairedScoreProduct_le_exp T ha
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg
    (K * pairedPermanentErrorBudget n 0 (scoreVariance T) +
      C * (scoreVariance T / n + Real.sqrt (scoreVariance T / n) + 1 / n) + D / n))
  rw [← Real.exp_add] at hm
  have heT := Real.exp_le_exp.mpr (he (scoreVariance T) hτ hvar)
  have hexp : Real.exp
      (-scoreVariance T + (K * pairedPermanentErrorBudget n 0 (scoreVariance T) +
        C * (scoreVariance T / n + Real.sqrt (scoreVariance T / n) + 1 / n) + D / n)) ≤
      Real.exp (fullScoreAbsorptionExponent K C D / n) := by
    convert heT using 1
    congr 1
    ring
  exact (hm.trans hexp).trans (exp_div_le_one_add_constant hn _ (by
    unfold fullScoreAbsorptionExponent
    positivity))

end TournamentHamiltonian
