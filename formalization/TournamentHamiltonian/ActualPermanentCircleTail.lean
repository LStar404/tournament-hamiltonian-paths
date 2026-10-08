import TournamentHamiltonian.MeanProjectionComplex
import TournamentHamiltonian.PermanentAnalyticTail

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem centered_permanent_normalization (B : Matrix ι ι ℝ)
    (hp : 0 < Fintype.card ι) (z : ℂ) :
    (normalizedPermanentPolynomial
      ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).eval z =
        (Fintype.card ι : ℂ) ^ Fintype.card ι / ((Fintype.card ι).factorial : ℂ) *
          (Complex.ofRealHom.mapMatrix (averagingMatrix ι) +
            z • Complex.ofRealHom.mapMatrix B).permanent := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have he : (fun i j => 1 + z *
      ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B) i j) =
      (Fintype.card ι : ℂ) • (Complex.ofRealHom.mapMatrix (averagingMatrix ι) +
        z • Complex.ofRealHom.mapMatrix B) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, averagingMatrix, Matrix.of_apply, smul_eq_mul, mul_one]
    simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_inv, Complex.ofReal_natCast]
    field_simp
  rw [normalizedPermanentPolynomial_eval, he, Matrix.permanent_smul]
  ring

/-- Circle control of the actual normalized permanent polynomial. All inputs
are genuine norms of the real centered matrix. -/
theorem actual_normalized_permanent_circle_bound (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (R q C : ℝ)
    (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hRq : R * q < 1) (z : ℂ) (hz : ‖z‖ = R) :
    ‖(normalizedPermanentPolynomial
      ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).eval z‖ ≤
        Real.exp (R * C * Real.sqrt (Fintype.card ι) / (1 - R * q)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have hf : (0 : ℝ) < (Fintype.card ι).factorial := by exact_mod_cast Nat.factorial_pos _
  have h := real_centered_permanent_le_exponential B hB hp z q C hgap hC hF
    (by rwa [hz])
  rw [hz] at h
  rw [centered_permanent_normalization B hp z, norm_mul, norm_div, norm_pow,
    Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ ((Fintype.card ι : ℝ) ^ Fintype.card ι / (Fintype.card ι).factorial) *
        ((Fintype.card ι).factorial / (Fintype.card ι : ℝ) ^ Fintype.card ι *
          Real.exp (R * C * Real.sqrt (Fintype.card ι) / (1 - R * q))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

theorem actual_normalized_permanent_coefficient_bound (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (R q C : ℝ)
    (hR : 0 < R) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hRq : R * q < 1) (k : ℕ) :
    ‖(normalizedPermanentPolynomial
      ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).coeff k‖ ≤
        Real.exp (R * C * Real.sqrt (Fintype.card ι) / (1 - R * q)) / R ^ k := by
  exact polynomial_circle_coefficient_bound _ R _ hR (Real.exp_pos _).le
    (actual_normalized_permanent_circle_bound B hB hp R q C hgap hC hF hRq) k

/-- Absolute analytic tail for the actual permanent, with no circle bound
or coefficient bound left as an assumed premise. -/
theorem actual_normalized_permanent_tail_bound (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (R q C : ℝ)
    (hR : 1 < R) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hRq : R * q < 1) (M : ℕ) :
    (∑ k ∈ (normalizedPermanentPolynomial
      ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).support.filter (fun k => M < k),
      ‖(normalizedPermanentPolynomial
        ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).coeff k‖) ≤
          R / (R - 1) *
            Real.exp (R * C * Real.sqrt (Fintype.card ι) / (1 - R * q)) / R ^ M := by
  exact polynomial_circle_tail_bound _ R _ hR (Real.exp_pos _).le
    (actual_normalized_permanent_circle_bound B hB hp R q C hgap hC hF hRq) M

end TournamentHamiltonian
