import TournamentHamiltonian.CircularPermanentMoment
import TournamentHamiltonian.SpectralRadialMoments

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder ComplexOrder

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

noncomputable def psdSpectralFactor (H : Matrix ι ι ℂ) (hH : H.PosSemidef) : Matrix ι ι ℂ :=
  (hH.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => (Real.sqrt (hH.isHermitian.eigenvalues i) : ℂ))

omit [Fintype ι] in
theorem real_sqrt_diagonal_conjTranspose (d : ι → ℝ) :
    (Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ))).conjTranspose =
      Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

theorem real_sqrt_diagonal_squared (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)) *
      Matrix.diagonal (fun i => (Real.sqrt (d i) : ℂ)) =
        Matrix.diagonal (fun i => (d i : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd i)]

theorem psdSpectralFactor_self_mul_star (H : Matrix ι ι ℂ) (hH : H.PosSemidef) :
    psdSpectralFactor H hH * (psdSpectralFactor H hH).conjTranspose = H := by
  rw [psdSpectralFactor, Matrix.conjTranspose_mul, real_sqrt_diagonal_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc
      (Matrix.diagonal _) (Matrix.diagonal _),
    real_sqrt_diagonal_squared _ hH.eigenvalues_nonneg]
  have hs := hH.isHermitian.spectral_theorem
  change H = (hH.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) *
      (hH.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose at hs
  simpa only [Matrix.mul_assoc] using hs.symm

theorem psdSpectralFactor_star_mul_self (H : Matrix ι ι ℂ) (hH : H.PosSemidef) :
    (psdSpectralFactor H hH).conjTranspose * psdSpectralFactor H hH =
      Matrix.diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) := by
  unfold psdSpectralFactor
  rw [Matrix.conjTranspose_mul, real_sqrt_diagonal_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (Matrix.diagonal _)]
  have hu := Unitary.coe_star_mul_self hH.isHermitian.eigenvectorUnitary
  change (hH.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose *
    (hH.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) = 1 at hu
  rw [hu, Matrix.one_mul, real_sqrt_diagonal_squared _ hH.eigenvalues_nonneg]

theorem complex_mulVec_norm_squared (A : Matrix ι ι ℂ) (z : ι → ℂ) :
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

theorem radialPhaseValue_norm_squared {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (r : ℝ) (hr : 0 ≤ r) (j : ℕ) :
    ‖radialPhaseValue ζ r j‖ ^ 2 = r := by
  rw [radialPhaseValue, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_pow, hζ.norm'_eq_one hN,
    one_pow, mul_one, Real.sq_sqrt hr]

theorem psdSpectralFactor_radial_norm_squared {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (H : Matrix ι ι ℂ) (hH : H.PosSemidef)
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (θ : ι → Fin N) :
    (∑ i, ‖(psdSpectralFactor H hH *ᵥ
      (fun j => radialPhaseValue ζ (r j) (θ j).val)) i‖ ^ 2) =
        ∑ i, hH.isHermitian.eigenvalues i * r i := by
  rw [complex_mulVec_norm_squared, psdSpectralFactor_star_mul_self]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  have h := radialPhaseValue_norm_squared hζ hN (r i) (hr i) (θ i).val
  rw [mul_left_comm, mul_comm (star _) (radialPhaseValue _ _ _)]
  change ((hH.isHermitian.eigenvalues i : ℂ) *
      (radialPhaseValue ζ (r i) (θ i).val *
        (starRingEnd ℂ) (radialPhaseValue ζ (r i) (θ i).val))).re = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem linearFormProduct_squared_re (A : Matrix ι ι ℂ) (z : ι → ℂ) :
    (linearFormProduct A z * star (linearFormProduct A z)).re =
      ∏ i, ‖(A *ᵥ z) i‖ ^ 2 := by
  change (linearFormProduct A z * (starRingEnd ℂ) (linearFormProduct A z)).re = _
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    linearFormProduct, norm_prod, ← Finset.prod_pow]
  rfl

theorem finitePhaseAverage_re_bound (N : ℕ) (hN : 0 < N)
    (f : (ι → Fin N) → ℂ) (M : ℝ) (h : ∀ θ, (f θ).re ≤ M) :
    (finitePhaseAverage N f).re ≤ M := by
  unfold finitePhaseAverage
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
  rw [Complex.div_ofReal_re, Complex.re_sum]
  apply (div_le_iff₀ (pow_pos (by exact_mod_cast hN) _)).mpr
  calc
    _ ≤ ∑ _ : ι → Fin N, M := Finset.sum_le_sum (fun θ _ => h θ)
    _ = _ := by simp; ring

theorem circularSpectralFactor_amgm {N : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0) (hp : 0 < Fintype.card ι)
    (H : Matrix ι ι ℂ) (hH : H.PosSemidef)
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (circularLinearProductSquared N ζ (psdSpectralFactor H hH) r).re ≤
      (∑ i, hH.isHermitian.eigenvalues i * r i) ^ Fintype.card ι /
        (Fintype.card ι : ℝ) ^ Fintype.card ι := by
  apply finitePhaseAverage_re_bound N (Nat.pos_of_ne_zero hN)
  intro θ
  rw [linearFormProduct_squared_re]
  have h := complex_vector_product_amgm
    (psdSpectralFactor H hH *ᵥ (fun j => radialPhaseValue ζ (r j) (θ j).val)) hp
  rwa [psdSpectralFactor_radial_norm_squared hζ hN H hH r hr θ] at h

/-- The full PSD permanent AM-GM bound, with the actual eigenvalues and
the actual complete homogeneous polynomial. -/
theorem complex_posSemidef_permanent_le_homogeneous (H : Matrix ι ι ℂ)
    (hH : H.PosSemidef) (hp : 0 < Fintype.card ι) :
    H.permanent.re ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        spectralHomogeneousPolynomial hH.isHermitian.eigenvalues (Fintype.card ι) := by
  let N := Fintype.card ι + 1
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hN : N ≠ 0 := by omega
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN
  have hdegree : Fintype.card ι < N := by omega
  let A := psdSpectralFactor H hH
  have hleft := circularLinearProductSquared_integrable hζ hN hdegree A
  have hright := (radial_weighted_power_integrable hH.isHermitian.eigenvalues
    (Fintype.card ι)).div_const ((Fintype.card ι : ℝ) ^ Fintype.card ι)
  have hpos : ∀ᵐ r : ι → ℝ ∂radialProductMeasure ι, ∀ i, 0 < r i := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually radialExpMeasure_ae_pos
  have h := integral_mono_ae hleft.re hright (by
    filter_upwards [hpos] with r hr
    exact circularSpectralFactor_amgm hζ hN hp H hH r (fun i => (hr i).le))
  have hidentity : (∫ r, RCLike.re (circularLinearProductSquared N ζ A r)
      ∂radialProductMeasure ι) = H.permanent.re := by
    rw [integral_re hleft, ← gramPermanent_eq_circular_moment hζ hN hdegree,
      psdSpectralFactor_self_mul_star]
    exact RCLike.re_to_complex
  rw [hidentity, integral_div, radial_weighted_power_moment] at h
  convert h using 1
  ring

end TournamentHamiltonian
