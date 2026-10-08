import TournamentHamiltonian.GaussianSeries
import Mathlib.Algebra.Order.Floor.Semiring

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

/-- A nonnegative convergent series inherits a true tail bound from its
weighted series; no coefficient estimate is assumed. -/
theorem nonnegative_weighted_series_tail_bound (g : ℕ → ℝ) (Γ σ : ℝ)
    (hg : ∀ k, 0 ≤ g k) (hs : Summable g)
    (hw : HasSum (fun k => g k * σ ^ k) Γ) (hσ : 1 < σ) (M : ℕ) :
    (∑' k, g (k + (M + 1))) ≤ Γ / σ ^ (M + 1) := by
  have hσp : 0 < σ := by linarith
  have htail := (summable_nat_add_iff (M + 1)).mpr hs
  have hwtail := (summable_nat_add_iff (M + 1)).mpr hw.summable
  have hpoint (k : ℕ) : g (k + (M + 1)) ≤
      (g (k + (M + 1)) * σ ^ (k + (M + 1))) / σ ^ (M + 1) := by
    apply (le_div_iff₀ (pow_pos hσp _)).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hσ.le (by omega)) (hg _)
  have hcomp := Summable.tsum_le_tsum hpoint htail (hwtail.div_const (σ ^ (M + 1)))
  rw [tsum_div_const] at hcomp
  have hwhole := Summable.sum_add_tsum_nat_add (M + 1) hw.summable
  rw [hw.tsum_eq] at hwhole
  have hfinite : 0 ≤ ∑ k ∈ Finset.range (M + 1), g k * σ ^ k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hg k) (pow_nonneg hσp.le k))
  exact hcomp.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hσp.le _))

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ]

/-- The actual Gaussian Wick coefficient tail is bounded by its actual Gram
determinant at any radius inside the operator-norm gap. -/
theorem bilinearGaussianCoefficient_tail_bound (Z : Matrix ι ρ ℝ) (σ : ℝ)
    (hσ : 1 < σ) (hgap : σ * ‖Z‖ < 1) (M : ℕ) :
    (∑' k, bilinearGaussianCoefficient Z (k + (M + 1))) ≤
      gramGaussian (σ • Z) / σ ^ (M + 1) := by
  have hn : ‖Z‖ < 1 := by
    have hm := mul_nonneg (sub_nonneg.mpr hσ.le) (norm_nonneg Z)
    nlinarith
  have hs : Summable (bilinearGaussianCoefficient Z) := by
    simpa only [one_pow, mul_one] using
      (bilinearGaussianCoefficient_hasSum Z 1 (by simpa using hn)).summable
  exact nonnegative_weighted_series_tail_bound _ _ σ
    (bilinearGaussianCoefficient_nonneg Z) hs
    (bilinearGaussianCoefficient_hasSum Z σ (by
      simpa only [abs_of_pos (by linarith : 0 < σ)] using hgap)) hσ M

theorem bilinearGaussianCoefficient_tail_summable (Z : Matrix ι ρ ℝ) (σ : ℝ)
    (hσ : 1 < σ) (hgap : σ * ‖Z‖ < 1) (M : ℕ) :
    Summable (fun k => bilinearGaussianCoefficient Z (k + (M + 1))) := by
  have hn : ‖Z‖ < 1 := by
    have hm := mul_nonneg (sub_nonneg.mpr hσ.le) (norm_nonneg Z)
    nlinarith
  apply (summable_nat_add_iff (M + 1)).mpr
  simpa only [one_pow, mul_one] using
    (bilinearGaussianCoefficient_hasSum Z 1 (by simpa using hn)).summable

/-- At the floor cutoff this is slightly stronger than the manuscript's
Gaussian tail estimate, as the leading factor σ is unnecessary. -/
theorem bilinearGaussianCoefficient_floor_tail_bound (Z : Matrix ι ρ ℝ) (σ a : ℝ)
    (hσ : 1 < σ) (hgap : σ * ‖Z‖ < 1) :
    (∑' k, bilinearGaussianCoefficient Z (k + (Nat.floor a + 1))) ≤
      gramGaussian (σ • Z) * Real.exp (-a * Real.log σ) := by
  have hσp : 0 < σ := by linarith
  have hΓ : 0 ≤ gramGaussian (σ • Z) := by
    unfold gramGaussian
    positivity
  have hinv : (σ ^ (Nat.floor a + 1))⁻¹ =
      Real.exp (-((Nat.floor a + 1 : ℕ) : ℝ) * Real.log σ) := by
    rw [neg_mul, Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hσp _)]
  have ha : a ≤ ((Nat.floor a + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one a).le
  calc
    _ ≤ gramGaussian (σ • Z) / σ ^ (Nat.floor a + 1) :=
      bilinearGaussianCoefficient_tail_bound Z σ hσ hgap (Nat.floor a)
    _ = gramGaussian (σ • Z) *
        Real.exp (-((Nat.floor a + 1 : ℕ) : ℝ) * Real.log σ) := by rw [div_eq_mul_inv, hinv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by nlinarith [Real.log_pos hσ])) hΓ

end TournamentHamiltonian
