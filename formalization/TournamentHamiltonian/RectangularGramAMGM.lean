import TournamentHamiltonian.HomogeneousGeometricBound

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder ComplexOrder

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem rectangular_complex_mulVec_norm_squared (A : Matrix κ ι ℂ) (z : ι → ℂ) :
    (∑ i, ‖(A *ᵥ z) i‖ ^ 2) =
      (dotProduct (star z) ((A.conjTranspose * A) *ᵥ z)).re := by
  have hquad : dotProduct (star (A *ᵥ z)) (A *ᵥ z) =
      dotProduct (star z) ((A.conjTranspose * A) *ᵥ z) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [← hquad]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]
  change ‖(A *ᵥ z) i‖ ^ 2 = ((A *ᵥ z) i * (starRingEnd ℂ) ((A *ᵥ z) i)).re
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem rectangular_linearFormProduct_squared_re (A : Matrix κ ι ℂ) (z : ι → ℂ) :
    (linearFormProduct A z * star (linearFormProduct A z)).re =
      ∏ i, ‖(A *ᵥ z) i‖ ^ 2 := by
  change (linearFormProduct A z * (starRingEnd ℂ) (linearFormProduct A z)).re = _
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    linearFormProduct, norm_prod, ← Finset.prod_pow]
  rfl

theorem rectangular_diagonalGram_radial_norm_squared {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (A : Matrix κ ι ℂ) (d : ι → ℝ)
    (hA : A.conjTranspose * A = Matrix.diagonal (fun i => (d i : ℂ)))
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (θ : ι → Fin N) :
    (∑ i, ‖(A *ᵥ (fun j => radialPhaseValue ζ (r j) (θ j).val)) i‖ ^ 2) =
        ∑ i, d i * r i := by
  rw [rectangular_complex_mulVec_norm_squared, hA]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  have h := radialPhaseValue_norm_squared hζ hN (r i) (hr i) (θ i).val
  rw [mul_left_comm, mul_comm (star _) (radialPhaseValue _ _ _)]
  change ((d i : ℂ) * (radialPhaseValue ζ (r i) (θ i).val *
      (starRingEnd ℂ) (radialPhaseValue ζ (r i) (θ i).val))).re = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Rectangular Gram factors permit additional independent circular variables;
the dimension factor is the number of rows, regardless of the number of columns. -/
theorem rectangularGramPermanent_le_homogeneous (A : Matrix κ ι ℂ) (d : ι → ℝ)
    (hA : A.conjTranspose * A = Matrix.diagonal (fun i => (d i : ℂ)))
    (hp : 0 < Fintype.card κ) :
    (A * A.conjTranspose).permanent.re ≤ (Fintype.card κ).factorial /
      (Fintype.card κ : ℝ) ^ Fintype.card κ *
        spectralHomogeneousPolynomial d (Fintype.card κ) := by
  let N := Fintype.card κ + 1
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hN : N ≠ 0 := by omega
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hdegree : Fintype.card κ < N := by omega
  have hleft := circularLinearProductSquared_integrable hζ hN hdegree A
  have hright := (radial_weighted_power_integrable d (Fintype.card κ)).div_const
    ((Fintype.card κ : ℝ) ^ Fintype.card κ)
  have hpos : ∀ᵐ r : ι → ℝ ∂radialProductMeasure ι, ∀ i, 0 < r i := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually radialExpMeasure_ae_pos
  have h := integral_mono_ae hleft.re hright (by
    filter_upwards [hpos] with r hr
    apply finitePhaseAverage_re_bound N (Nat.pos_of_ne_zero hN)
    intro θ
    rw [rectangular_linearFormProduct_squared_re]
    have hh := complex_vector_product_amgm
      (A *ᵥ (fun j => radialPhaseValue ζ (r j) (θ j).val)) hp
    rwa [rectangular_diagonalGram_radial_norm_squared hζ hN A d hA r
      (fun i => (hr i).le) θ] at hh)
  have hidentity : (∫ r, RCLike.re (circularLinearProductSquared N ζ A r)
      ∂radialProductMeasure ι) = (A * A.conjTranspose).permanent.re := by
    rw [integral_re hleft, ← gramPermanent_eq_circular_moment hζ hN hdegree]
    exact RCLike.re_to_complex
  rw [hidentity, integral_div, radial_weighted_power_moment] at h
  convert h using 1
  ring

theorem rectangularGramPermanent_le_geometric (A : Matrix κ ι ℂ) (d : ι → ℝ)
    (hA : A.conjTranspose * A = Matrix.diagonal (fun i => (d i : ℂ)))
    (hp : 0 < Fintype.card κ) (i₀ : ι) (hd : ∀ i, 0 ≤ d i)
    (h₀ : d i₀ = 1) (h1 : ∀ i, i ≠ i₀ → d i < 1) :
    (A * A.conjTranspose).permanent.re ≤ (Fintype.card κ).factorial /
      (Fintype.card κ : ℝ) ^ Fintype.card κ *
        ∏ i : {i : ι // i ≠ i₀}, (1 - d i.val)⁻¹ :=
  (rectangularGramPermanent_le_homogeneous A d hA hp).trans
    (mul_le_mul_of_nonneg_left (spectralHomogeneousPolynomial_le_geometric d i₀ hd h₀ h1 _)
      (by positivity))

end TournamentHamiltonian
