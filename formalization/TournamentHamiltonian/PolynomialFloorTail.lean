import TournamentHamiltonian.PermanentAnalyticTail
import Mathlib.Algebra.Order.Floor.Semiring

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

theorem polynomial_circle_tail_bound_succ (p : Polynomial ℂ) (R A : ℝ)
    (hR : 1 < R) (hA : 0 ≤ A)
    (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ A) (M : ℕ) :
    (∑ k ∈ p.support.filter (fun k => M < k), ‖p.coeff k‖) ≤
      R / (R - 1) * A / R ^ (M + 1) := by
  let N := max (M + 1) (p.natDegree + 1)
  have hsub : p.support.filter (fun k => M < k) ⊆ Finset.Ico (M + 1) N := by
    intro k hk
    obtain ⟨hk, hm⟩ := Finset.mem_filter.mp hk
    have hd := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    exact Finset.mem_Ico.mpr ⟨by omega,
      lt_of_lt_of_le (by omega : k < p.natDegree + 1) (le_max_right _ _)⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)).trans
  exact polynomial_circle_finite_tail_bound p R A hR hA hcircle (M + 1) N (le_max_left _ _)

/-- The extra first power in the strict tail aligns exactly with a floor
cutoff, retaining the manuscript's factor R/(R-1). -/
theorem polynomial_circle_exponential_tail_bound (p : Polynomial ℂ) (R β a : ℝ)
    (hR : 1 < R) (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ Real.exp β)
    (M : ℕ) (ha : a ≤ (M + 1 : ℕ)) :
    (∑ k ∈ p.support.filter (fun k => M < k), ‖p.coeff k‖) ≤
      R / (R - 1) * Real.exp (β - a * Real.log R) := by
  have hRp : 0 < R := by linarith
  have hinv : (R ^ (M + 1))⁻¹ = Real.exp (-((M + 1 : ℕ) : ℝ) * Real.log R) := by
    rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hRp _)]
  calc
    _ ≤ R / (R - 1) * Real.exp β / R ^ (M + 1) :=
      polynomial_circle_tail_bound_succ p R _ hR (Real.exp_pos _).le hcircle M
    _ = R / (R - 1) * Real.exp (β - ((M + 1 : ℕ) : ℝ) * Real.log R) := by
      rw [div_eq_mul_inv, hinv, mul_assoc, ← Real.exp_add]
      simp only [sub_eq_add_neg, neg_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [Real.log_pos hR])) (by positivity)

theorem polynomial_circle_floor_tail_bound (p : Polynomial ℂ) (R β a : ℝ)
    (hR : 1 < R) (hcircle : ∀ z : ℂ, ‖z‖ = R → ‖p.eval z‖ ≤ Real.exp β) :
    (∑ k ∈ p.support.filter (fun k => Nat.floor a < k), ‖p.coeff k‖) ≤
      R / (R - 1) * Real.exp (β - a * Real.log R) := by
  exact polynomial_circle_exponential_tail_bound p R β a hR hcircle (Nat.floor a)
    (by simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one a).le)

end TournamentHamiltonian
