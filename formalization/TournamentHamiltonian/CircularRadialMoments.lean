import TournamentHamiltonian.ExponentialRadialMoments
import TournamentHamiltonian.FinitePhaseOrthogonality
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def radialPhaseValue (ζ : ℂ) (r : ℝ) (j : ℕ) : ℂ :=
  (Real.sqrt r : ℂ) * ζ ^ j

theorem radial_phase_mixed_average {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (r : ℝ) (hr : 0 ≤ r)
    (a b : ℕ) (ha : a < N) (hb : b < N) :
    (∑ j : Fin N, (radialPhaseValue ζ r j.val) ^ a *
      star ((radialPhaseValue ζ r j.val) ^ b)) / (N : ℂ) =
      if a = b then ((r ^ a : ℝ) : ℂ) else 0 := by
  have hexpand : ∀ j : Fin N,
      (radialPhaseValue ζ r j.val) ^ a * star ((radialPhaseValue ζ r j.val) ^ b) =
      ((Real.sqrt r : ℂ) ^ a * (Real.sqrt r : ℂ) ^ b) *
      ((ζ ^ j.val) ^ a * star ((ζ ^ j.val) ^ b)) := by
    intro j
    have hreal : star (Real.sqrt r : ℂ) = (Real.sqrt r : ℂ) := by
      simp only [Complex.star_def, Complex.conj_ofReal]
    simp only [radialPhaseValue, mul_pow, star_mul, star_pow, hreal]
    ring
  simp_rw [hexpand]
  rw [← Finset.mul_sum, root_phase_cross_sum hζ hN a b ha hb]
  split_ifs with hab
  · subst b
    have hsq : (Real.sqrt r : ℂ) ^ a * (Real.sqrt r : ℂ) ^ a = (r ^ a : ℝ) := by
      rw [← mul_pow, ← Complex.ofReal_mul, Real.mul_self_sqrt hr, Complex.ofReal_pow]
    rw [hsq, mul_div_cancel_right₀ _ (by exact_mod_cast hN)]
  · simp

/-- Exact factorial moments of the actual radial measure and actual finite phases. -/
theorem circular_radial_mixed_moment {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (a b : ℕ)
    (ha : a < N) (hb : b < N) :
    (∫ r, (∑ j : Fin N, (radialPhaseValue ζ r j.val) ^ a *
      star ((radialPhaseValue ζ r j.val) ^ b)) / (N : ℂ) ∂radialExpMeasure) =
      if a = b then (a.factorial : ℂ) else 0 := by
  rw [integral_congr_ae (show (fun r => (∑ j : Fin N,
      (radialPhaseValue ζ r j.val) ^ a * star ((radialPhaseValue ζ r j.val) ^ b)) /
      (N : ℂ)) =ᵐ[radialExpMeasure] (fun r => if a = b then (r ^ a : ℝ) else 0) from by
    filter_upwards [radialExpMeasure_ae_pos] with r hr
    exact radial_phase_mixed_average hζ hN r hr.le a b ha hb)]
  split_ifs
  · rw [integral_complex_ofReal, radialExpMeasure_pow_moment]
    simp
  · simp

variable {ι : Type*} [Fintype ι]

noncomputable def radialProductMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => radialExpMeasure)

theorem radial_product_pow_moment (a : ι → ℕ) :
    (∫ r : ι → ℝ, ∏ i, (r i) ^ a i ∂radialProductMeasure ι) =
      ∏ i, ((a i).factorial : ℝ) := by
  change (∫ r, ∏ i, (fun i (x : ℝ) => x ^ a i) i (r i)
    ∂Measure.pi (fun _ : ι => radialExpMeasure)) = _
  have h := integral_fintype_prod_eq_prod (fun i (x : ℝ) => x ^ a i)
    (μ := fun _ : ι => radialExpMeasure)
  simpa only [radialExpMeasure_pow_moment] using h

theorem radial_product_pow_integrable (a : ι → ℕ) :
    Integrable (fun r : ι → ℝ => ∏ i, (r i) ^ a i) (radialProductMeasure ι) :=
  Integrable.fintype_prod (fun i => radialExpMeasure_integrable_pow (a i))

noncomputable def finitePhaseAverage (N : ℕ) (f : (ι → Fin N) → ℂ) : ℂ :=
  (∑ θ, f θ) / (N : ℂ) ^ Fintype.card ι

theorem finitePhaseAverage_product (N : ℕ) (f : ι → Fin N → ℂ) :
    finitePhaseAverage N (fun θ => ∏ i, f i (θ i)) =
      ∏ i, ((∑ j, f i j) / (N : ℂ)) := by
  classical
  rw [finitePhaseAverage, ← Fintype.prod_sum, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]

theorem circular_radial_product_mixed_average {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (a b : ι → ℕ) (ha : ∀ i, a i < N) (hb : ∀ i, b i < N) :
    finitePhaseAverage N (fun θ => ∏ i, (radialPhaseValue ζ (r i) (θ i).val) ^ a i *
      star ((radialPhaseValue ζ (r i) (θ i).val) ^ b i)) =
      if a = b then ((∏ i, (r i) ^ a i : ℝ) : ℂ) else 0 := by
  classical
  rw [finitePhaseAverage_product N
    (fun i (j : Fin N) => (radialPhaseValue ζ (r i) j.val) ^ a i *
      star ((radialPhaseValue ζ (r i) j.val) ^ b i))]
  simp_rw [radial_phase_mixed_average hζ hN _ (hr _) _ _ (ha _) (hb _)]
  by_cases hab : a = b
  · subst b
    simp [Complex.ofReal_prod]
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem circular_radial_product_mixed_moment {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    (a b : ι → ℕ) (ha : ∀ i, a i < N) (hb : ∀ i, b i < N) :
    (∫ r : ι → ℝ, finitePhaseAverage N (fun θ =>
      ∏ i, (radialPhaseValue ζ (r i) (θ i).val) ^ a i *
      star ((radialPhaseValue ζ (r i) (θ i).val) ^ b i)) ∂radialProductMeasure ι) =
      if a = b then (∏ i, ((a i).factorial : ℂ)) else 0 := by
  classical
  have hpos : ∀ᵐ r : ι → ℝ ∂radialProductMeasure ι, ∀ i, 0 < r i := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually radialExpMeasure_ae_pos
  rw [integral_congr_ae (show _ =ᵐ[radialProductMeasure ι]
      (fun r : ι → ℝ => if a = b then ((∏ i, (r i) ^ a i : ℝ) : ℂ) else 0) from by
    filter_upwards [hpos] with r hr
    exact circular_radial_product_mixed_average hζ hN r (fun i => (hr i).le) a b ha hb)]
  split_ifs
  · rw [integral_complex_ofReal, radial_product_pow_moment]
    simp
  · simp

end TournamentHamiltonian
