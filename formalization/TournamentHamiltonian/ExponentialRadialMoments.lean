import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

/-- An actual radial exponential measure, supported on the positive real axis. -/
noncomputable def radialExpMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (Real.exp (-x)))

theorem radialExpMeasure_eq_expMeasure :
    radialExpMeasure = ProbabilityTheory.expMeasure 1 := by
  rw [radialExpMeasure, restrict_Ioi_eq_restrict_Ici,
    ← withDensity_indicator measurableSet_Ici]
  unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  congr 1
  ext x
  simp only [Set.indicator_apply, Set.mem_Ici, ProbabilityTheory.gammaPDF_eq,
    Real.one_rpow, Real.Gamma_one, div_one, sub_self, Real.rpow_zero,
    mul_one, one_mul]
  split_ifs <;> simp

instance radialExpMeasure_probability : IsProbabilityMeasure radialExpMeasure := by
  rw [radialExpMeasure_eq_expMeasure]
  exact ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one

theorem radialExpMeasure_ae_pos : ∀ᵐ x ∂radialExpMeasure, 0 < x :=
  withDensity_absolutelyContinuous _ _
    (self_mem_ae_restrict measurableSet_Ioi)

theorem radialExpMeasure_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂radialExpMeasure) = ∫ x in Ioi 0, Real.exp (-x) * f x := by
  exact integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
    f |>.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]))

theorem radialExpMeasure_integrable_rpow (s : ℝ) (hs : -1 < s) :
    Integrable (fun x => x ^ s) radialExpMeasure := by
  rw [radialExpMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have h := Real.GammaIntegral_convergent (s := s + 1) (by linarith)
  simpa only [IntegrableOn, add_sub_cancel_right, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    smul_eq_mul] using h

theorem radialExpMeasure_rpow_moment (s : ℝ) (hs : -1 < s) :
    (∫ x, x ^ s ∂radialExpMeasure) = Real.Gamma (s + 1) := by
  rw [radialExpMeasure_integral]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := s + 1) (r := 1) (by linarith) zero_lt_one
  simpa only [add_sub_cancel_right, one_mul, one_div_one, Real.one_rpow,
    mul_one, mul_comm] using h

theorem radialExpMeasure_integrable_pow (k : ℕ) :
    Integrable (fun x => x ^ k) radialExpMeasure := by
  simpa only [Real.rpow_natCast] using
    radialExpMeasure_integrable_rpow (k : ℝ) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

theorem radialExpMeasure_pow_moment (k : ℕ) :
    (∫ x, x ^ k ∂radialExpMeasure) = (k.factorial : ℝ) := by
  simpa only [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using
    radialExpMeasure_rpow_moment (k : ℝ) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

end TournamentHamiltonian
