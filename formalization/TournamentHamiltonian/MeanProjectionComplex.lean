import TournamentHamiltonian.CenteredComplexPermanent
import TournamentHamiltonian.MatrixComplexification
import TournamentHamiltonian.LocalScaling

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

noncomputable def meanUnitColumn (ι : Type*) [Fintype ι] : Matrix ι Unit ℂ :=
  fun _ _ => ((Real.sqrt (Fintype.card ι))⁻¹ : ℝ)

theorem meanUnitColumn_unit (hp : 0 < Fintype.card ι) :
    (meanUnitColumn ι).conjTranspose * meanUnitColumn ι = 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hs := Real.sq_sqrt hn.le
  have hsn : Real.sqrt (Fintype.card ι) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  ext i j
  cases i; cases j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, meanUnitColumn,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Matrix.one_apply_eq, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  norm_cast
  field_simp
  nlinarith

theorem meanUnitColumn_projection (_hp : 0 < Fintype.card ι) :
    meanUnitColumn ι * (meanUnitColumn ι).conjTranspose =
      Complex.ofRealHom.mapMatrix (averagingMatrix ι) := by
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, meanUnitColumn,
    Complex.star_def, Complex.conj_ofReal, Fintype.sum_unique, averagingMatrix, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply, mul_one, RingHom.mapMatrix_apply, Matrix.map_apply,
    ← Complex.ofReal_mul]
  congr 1
  rw [← mul_inv, ← pow_two, Real.sq_sqrt hn]

theorem complexification_averaging_mul_zero (B : Matrix ι ι ℝ) (hB : DoublyCentered B) :
    Complex.ofRealHom.mapMatrix (averagingMatrix ι) * Complex.ofRealHom.mapMatrix B = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg (Complex.ofRealHom.mapMatrix : Matrix ι ι ℝ → Matrix ι ι ℂ) hB.averaging_mul

theorem complexification_mul_averaging_zero (B : Matrix ι ι ℝ) (hB : DoublyCentered B) :
    Complex.ofRealHom.mapMatrix B * Complex.ofRealHom.mapMatrix (averagingMatrix ι) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg (Complex.ofRealHom.mapMatrix : Matrix ι ι ℝ → Matrix ι ι ℂ) hB.mul_averaging

/-- Actual real L2 and Frobenius hypotheses imply the complex permanent
circle majorant, after passing through a proved unit-column Gram factor. -/
theorem real_centered_permanent_le_exponential (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (z : ℂ) (q C : ℝ)
    (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hzq : ‖z‖ * q < 1) :
    ‖(Complex.ofRealHom.mapMatrix (averagingMatrix ι) +
        z • Complex.ofRealHom.mapMatrix B).permanent‖ ≤
      (Fintype.card ι).factorial / (Fintype.card ι : ℝ) ^ Fintype.card ι *
        Real.exp (‖z‖ * C * Real.sqrt (Fintype.card ι) / (1 - ‖z‖ * q)) := by
  rw [← meanUnitColumn_projection hp]
  exact centered_complex_permanent_le_exponential _ (meanUnitColumn_unit hp) _
    (by rw [meanUnitColumn_projection hp]; exact complexification_averaging_mul_zero B hB)
    (by rw [meanUnitColumn_projection hp]; exact complexification_mul_averaging_zero B hB)
    hp z q C (by rwa [← real_matrix_opNorm_eq_complexification]) hC
    (by rw [complexFrobeniusSq_ofReal];
        exact pow_le_pow_left₀ (realFrobeniusNorm_nonneg B) hF 2) hzq

end TournamentHamiltonian
