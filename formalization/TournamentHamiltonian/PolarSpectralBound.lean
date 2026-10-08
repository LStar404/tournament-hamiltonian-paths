import TournamentHamiltonian.PermanentSpectralEnvelope

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem complex_abs_posSemidef (Z : Matrix ι ι ℂ) : (CFC.abs Z).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg Z)

theorem complex_psd_exponential_bound_full_dimension (H : Matrix ι ι ℂ)
    (hH : H.PosSemidef) (i₀ : ι) (h₀ : hH.isHermitian.eigenvalues i₀ = 1)
    (q C : ℝ) (hq : q < 1) (hC : 0 ≤ C)
    (hgap : ∀ i, i ≠ i₀ → hH.isHermitian.eigenvalues i ≤ q)
    (hL2 : ∑ i : {i : ι // i ≠ i₀}, (hH.isHermitian.eigenvalues i.val) ^ 2 ≤ C ^ 2) :
    H.permanent.re ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (C * Real.sqrt (Fintype.card ι) / (1 - q)) := by
  apply (complex_posSemidef_permanent_le_exponential H hH i₀ h₀ q C hq hC hgap hL2).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.sqrt_le_sqrt
  exact_mod_cast Fintype.card_subtype_le (fun i : ι => i ≠ i₀)

/-- Arbitrary nonnormal and singular inputs: the exponential envelope follows
from the actual polar spectral data, retaining the essential factorial factor. -/
theorem complex_permanent_le_exponential_spectral (Z : Matrix ι ι ℂ)
    (iL iR : ι) (q C : ℝ) (hq : q < 1) (hC : 0 ≤ C)
    (hLone : (complex_abs_posSemidef Z.conjTranspose).isHermitian.eigenvalues iL = 1)
    (hRone : (complex_abs_posSemidef Z).isHermitian.eigenvalues iR = 1)
    (hLgap : ∀ i, i ≠ iL →
      (complex_abs_posSemidef Z.conjTranspose).isHermitian.eigenvalues i ≤ q)
    (hRgap : ∀ i, i ≠ iR → (complex_abs_posSemidef Z).isHermitian.eigenvalues i ≤ q)
    (hLL2 : ∑ i : {i : ι // i ≠ iL},
      ((complex_abs_posSemidef Z.conjTranspose).isHermitian.eigenvalues i.val) ^ 2 ≤ C ^ 2)
    (hRL2 : ∑ i : {i : ι // i ≠ iR},
      ((complex_abs_posSemidef Z).isHermitian.eigenvalues i.val) ^ 2 ≤ C ^ 2) :
    ‖Z.permanent‖ ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (C * Real.sqrt (Fintype.card ι) / (1 - q)) := by
  have hL := complex_psd_exponential_bound_full_dimension _
    (complex_abs_posSemidef Z.conjTranspose) iL hLone q C hq hC hLgap hLL2
  have hR := complex_psd_exponential_bound_full_dimension _
    (complex_abs_posSemidef Z) iR hRone q C hq hC hRgap hRL2
  have hL0 := (Complex.nonneg_iff.mp
    (complex_posSemidef_permanent_nonnegative _ (complex_abs_posSemidef Z.conjTranspose))).1
  have hR0 := (Complex.nonneg_iff.mp
    (complex_posSemidef_permanent_nonnegative _ (complex_abs_posSemidef Z))).1
  have hpolar := complex_permanent_block_cauchy
    (CFC.abs Z.conjTranspose) Z (CFC.abs Z) (permanent_polarization_block_posSemidef Z)
  have hprod := mul_le_mul hL hR hR0 (by positivity)
  have hnonneg : 0 ≤ (Fintype.card ι).factorial /
      (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (C * Real.sqrt (Fintype.card ι) / (1 - q)) := by positivity
  nlinarith [norm_nonneg Z.permanent]

end TournamentHamiltonian
