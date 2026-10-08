import TournamentHamiltonian.PermanentExpansion
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Complex MeasureTheory

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

/-- The coefficient estimate is obtained from the actual circle values of a
polynomial, via Parseval, rather than assumed as a bound on coefficients. -/
theorem polynomial_circle_coefficient_bound (p : Polynomial ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A) (k : ℕ) :
    ‖p.coeff k‖ ≤ A / R ^ k := by
  let q := p.comp (Polynomial.C (R : ℂ) * Polynomial.X)
  have hcont : Continuous (fun z : ℂ => ‖q.eval z‖ ^ 2) := by fun_prop
  have havg : Real.circleAverage (fun z : ℂ => ‖q.eval z‖ ^ 2) 0 1 ≤ A ^ 2 :=
    Real.circleAverage_mono_on_of_le_circle hcont.continuousOn.circleIntegrable' (by
      intro z hz
      have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hq : q.eval z = p.eval ((R : ℂ) * z) := by simp [q, Polynomial.eval_comp]
      have hn : ‖(R : ℂ) * z‖ = R := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hz1, mul_one]
      rw [hq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcircle _ hn) 2)
  have hs : ‖q.coeff k‖ ^ 2 ≤ ∑ i ∈ q.support, ‖q.coeff i‖ ^ 2 := by
    by_cases hk : k ∈ q.support
    · exact Finset.single_le_sum (fun i _ => sq_nonneg ‖q.coeff i‖) hk
    · simp only [Polynomial.mem_support_iff, not_not] at hk
      rw [hk, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Polynomial.sum_sq_norm_coeff_eq_circleAverage] at hs
  have hcoef : ‖q.coeff k‖ = ‖p.coeff k‖ * R ^ k := by
    simp only [q, Polynomial.comp_C_mul_X_coeff, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hnorm : ‖q.coeff k‖ ≤ A := (sq_le_sq₀ (norm_nonneg _) hA).mp (hs.trans havg)
  rw [hcoef] at hnorm
  exact (le_div_iff₀ (pow_pos hR k)).mpr hnorm

theorem polynomial_circle_finite_tail_bound (p : Polynomial ℂ) (R A : ℝ)
    (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A)
    (M N : ℕ) (hMN : M ≤ N) :
    (∑ k ∈ Finset.Ico M N, ‖p.coeff k‖) ≤ R / (R - 1) * A / R ^ M := by
  have hRp : 0 < R := by linarith
  have hr : R⁻¹ < 1 := by apply (inv_lt_one₀ hRp).mpr; exact hR
  have hg : (∑ k ∈ Finset.Ico M N, (R⁻¹) ^ k) ≤ (R⁻¹) ^ M / (1 - R⁻¹) := by
    rw [geom_sum_Ico' (ne_of_lt hr) hMN]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (inv_nonneg.mpr hRp.le) N]) (by linarith)
  calc
    _ ≤ ∑ k ∈ Finset.Ico M N, A / R ^ k :=
      Finset.sum_le_sum (fun k _ => polynomial_circle_coefficient_bound p R A hRp hA hcircle k)
    _ = A * ∑ k ∈ Finset.Ico M N, (R⁻¹) ^ k := by simp only [Finset.mul_sum, div_eq_mul_inv, inv_pow]
    _ ≤ A * ((R⁻¹) ^ M / (1 - R⁻¹)) := mul_le_mul_of_nonneg_left hg hA
    _ = _ := by
      rw [inv_pow]
      field_simp

/-- The entire actual polynomial tail outside a finite coefficient window. -/
theorem polynomial_circle_tail_bound (p : Polynomial ℂ) (R A : ℝ)
    (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A) (M : ℕ) :
    (∑ k ∈ p.support.filter (fun k => M < k), ‖p.coeff k‖) ≤ R / (R - 1) * A / R ^ M := by
  let N := max M (p.natDegree + 1)
  have hsub : p.support.filter (fun k => M < k) ⊆ Finset.Ico M N := by
    intro k hk
    obtain ⟨hk, hm⟩ := Finset.mem_filter.mp hk
    apply Finset.mem_Ico.mpr
    have hd := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    exact ⟨hm.le, lt_of_lt_of_le (by omega : k < p.natDegree + 1) (le_max_right _ _)⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans
  exact polynomial_circle_finite_tail_bound p R A hR hA hcircle M N (le_max_left _ _)

theorem normalized_permanent_circle_tail_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι ℂ) (R A : ℝ) (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R →
      ‖Matrix.permanent (fun i j => 1 + z * E i j)‖ ≤ ((Fintype.card ι).factorial : ℝ) * A)
    (M : ℕ) :
    (∑ k ∈ (normalizedPermanentPolynomial E).support.filter (fun k => M < k),
      ‖(normalizedPermanentPolynomial E).coeff k‖) ≤ R / (R - 1) * A / R ^ M := by
  apply polynomial_circle_tail_bound _ R A hR hA _ M
  intro z hz
  rw [normalizedPermanentPolynomial_eval, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (show (0 : ℝ) < (Fintype.card ι).factorial by
    exact_mod_cast Nat.factorial_pos (Fintype.card ι))).mpr
  simpa only [mul_comm] using hcircle z hz

end TournamentHamiltonian
