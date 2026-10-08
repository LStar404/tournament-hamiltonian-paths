import TournamentHamiltonian.CircularRadialMoments
import Mathlib.Data.Nat.Choose.Multinomial

open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- The actual complete homogeneous polynomial of the eigenvalues. -/
noncomputable def spectralHomogeneousPolynomial (eigenvalues : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset ι) n, ∏ i, eigenvalues i ^ a i

theorem radial_weighted_power_integrable (eigenvalues : ι → ℝ) (n : ℕ) :
    Integrable (fun r : ι → ℝ => (∑ i, eigenvalues i * r i) ^ n) (radialProductMeasure ι) := by
  have h : Integrable (fun r : ι → ℝ =>
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
        (Nat.multinomial Finset.univ a : ℝ) * (∏ i, eigenvalues i ^ a i) * ∏ i, r i ^ a i)
      (radialProductMeasure ι) := by
    apply integrable_finsetSum
    intro a _
    exact (radial_product_pow_integrable a).const_mul _
  apply h.congr
  apply ae_of_all
  intro r
  change _ = (∑ i, eigenvalues i * r i) ^ n
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_pow, Finset.prod_mul_distrib]
  ring

theorem radial_weighted_power_moment (eigenvalues : ι → ℝ) (n : ℕ) :
    (∫ r : ι → ℝ, (∑ i, eigenvalues i * r i) ^ n ∂radialProductMeasure ι) =
      (n.factorial : ℝ) * spectralHomogeneousPolynomial eigenvalues n := by
  have hexpand : (fun r : ι → ℝ => (∑ i, eigenvalues i * r i) ^ n) =
      (fun r => ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
        (Nat.multinomial Finset.univ a : ℝ) * (∏ i, eigenvalues i ^ a i) * ∏ i, r i ^ a i) := by
    funext r
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    apply Finset.sum_congr rfl
    intro a _
    simp only [mul_pow, Finset.prod_mul_distrib]
    ring
  rw [hexpand, integral_finsetSum]
  · rw [spectralHomogeneousPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_const_mul, radial_product_pow_moment]
    have hs : (∑ i, a i) = n := (Finset.mem_piAntidiag.mp ha).1
    have h := Nat.multinomial_spec Finset.univ a
    rw [hs] at h
    have hR : (Nat.multinomial Finset.univ a : ℝ) *
        (∏ i, ((a i).factorial : ℝ)) = (n.factorial : ℝ) := by
      rw [mul_comm]
      exact_mod_cast h
    calc
      _ = ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, ((a i).factorial : ℝ)) *
          (∏ i, eigenvalues i ^ a i) := by ring
      _ = _ := by rw [hR]
  · intro a _
    exact (radial_product_pow_integrable a).const_mul _

end TournamentHamiltonian
