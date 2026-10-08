import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! Actual moments of standard Gaussian measures, derived from their proved moment-generating function. -/

namespace TournamentHamiltonian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def standardGaussianMoment (k : ℕ) : ℝ :=
  ∫ x : ℝ, x ^ k ∂gaussianReal 0 1

theorem standardGaussianMoment_eq_iteratedDeriv (k : ℕ) :
    standardGaussianMoment k = iteratedDeriv k (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1) (by simp) k
  simpa [standardGaussianMoment, mgf_id_gaussianReal, Pi.pow_apply] using h.symm

theorem standardGaussianMoment_zero : standardGaussianMoment 0 = 1 := by
  simp [standardGaussianMoment]

theorem standardGaussianMoment_one : standardGaussianMoment 1 = 0 := by
  simp [standardGaussianMoment]

private theorem deriv_standardGaussianMGF :
    deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => t * Real.exp (t ^ 2 / 2) := by
  ext t
  rw [deriv_exp (by fun_prop)]
  simp only [deriv_div_const, deriv_pow_field, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- The genuine Gaussian integration recurrence, proved by differentiating its MGF. -/
theorem standardGaussianMoment_add_two (k : ℕ) :
    standardGaussianMoment (k + 2) = (k + 1 : ℝ) * standardGaussianMoment k := by
  rw [standardGaussianMoment_eq_iteratedDeriv, standardGaussianMoment_eq_iteratedDeriv]
  rw [show k + 2 = (k + 1) + 1 by omega, iteratedDeriv_succ', deriv_standardGaussianMGF]
  change iteratedDeriv (k + 1) (id * (fun t : ℝ => Real.exp (t ^ 2 / 2))) 0 = _
  rw [iteratedDeriv_mul (by fun_prop) (by fun_prop)]
  rw [Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id]
  · intro i _ hi
    simp [iteratedDeriv_id, hi]
  · intro h
    simp at h

theorem standardGaussianMoment_odd (k : ℕ) :
    standardGaussianMoment (2 * k + 1) = 0 := by
  induction k with
  | zero => exact standardGaussianMoment_one
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      standardGaussianMoment_add_two, ih, mul_zero]

theorem standardGaussianMoment_even (k : ℕ) :
    standardGaussianMoment (2 * k) = ((2 * k - 1).doubleFactorial : ℝ) := by
  induction k with
  | zero => simpa using standardGaussianMoment_zero
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k) + 2 by omega, standardGaussianMoment_add_two, ih]
    rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega, Nat.doubleFactorial_add_one, Nat.cast_mul]
    norm_cast

theorem standardGaussianMoment_nonneg (k : ℕ) : 0 ≤ standardGaussianMoment k := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by omega, standardGaussianMoment_even]
    positivity
  · rw [standardGaussianMoment_odd]

theorem standardGaussianPow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  simpa only [id_eq] using
    integrable_pow_of_mem_interior_integrableExpSet (X := id) (μ := gaussianReal 0 1) (by simp) k

theorem standardGaussian_product_moment {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, (x i) ^ k i ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∏ i, standardGaussianMoment (k i) :=
  integral_fintype_prod_eq_prod (fun (i : ι) (x : ℝ) => x ^ k i)

theorem standardGaussian_product_integrable {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, (x i) ^ k i) (Measure.pi (fun _ => gaussianReal 0 1)) :=
  Integrable.fintype_prod (fun i => standardGaussianPow_integrable (k i))

end TournamentHamiltonian
