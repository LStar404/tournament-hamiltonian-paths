import TournamentHamiltonian.PermanentPolarization
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped BigOperators
open MeasureTheory

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

variable {ι : Type*} [Fintype ι]

theorem finite_nonnegative_product_amgm (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hp : 0 < Fintype.card ι) :
    (∏ i, a i) ≤ ((∑ i, a i) / Fintype.card ι) ^ Fintype.card ι := by
  have hpR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : ι => (1 : ℝ)) a
    (by intros; norm_num) (by simpa using hpR) (fun i _ => ha i)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hprod : 0 ≤ ∏ i, a i := Finset.prod_nonneg (fun i _ => ha i)
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hprod _) h (Fintype.card ι)
  have hpow : ((∏ i, a i) ^ (Fintype.card ι : ℝ)⁻¹) ^ Fintype.card ι = ∏ i, a i := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod, inv_mul_cancel₀ hpR.ne', Real.rpow_one]
  rwa [hpow] at hh

/-- The exact dimension factor needed by the PSD permanent comparison. -/
theorem complex_vector_product_amgm (z : ι → ℂ) (hp : 0 < Fintype.card ι) :
    (∏ i, ‖z i‖ ^ 2) ≤ (∑ i, ‖z i‖ ^ 2) ^ Fintype.card ι /
      (Fintype.card ι : ℝ) ^ Fintype.card ι := by
  simpa only [div_pow] using finite_nonnegative_product_amgm (fun i => ‖z i‖ ^ 2)
    (fun i => sq_nonneg _) hp

/-- Pointwise AM-GM is integrated against an actual measure; no stochastic
moment formula or permanent comparison is assumed here. -/
theorem complex_product_amgm_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ι → ℂ) (hp : 0 < Fintype.card ι)
    (hprod : Integrable (fun ω => ∏ i, ‖Z ω i‖ ^ 2) μ)
    (hpower : Integrable (fun ω => (∑ i, ‖Z ω i‖ ^ 2) ^ Fintype.card ι) μ) :
    (∫ ω, ∏ i, ‖Z ω i‖ ^ 2 ∂μ) ≤
      ((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹ *
        ∫ ω, (∑ i, ‖Z ω i‖ ^ 2) ^ Fintype.card ι ∂μ := by
  have hright := hpower.const_mul ((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹
  have h := integral_mono hprod hright (fun ω => by
    have h := complex_vector_product_amgm (Z ω) hp
    simpa only [div_eq_mul_inv, mul_comm] using h)
  rwa [integral_const_mul] at h

end TournamentHamiltonian
