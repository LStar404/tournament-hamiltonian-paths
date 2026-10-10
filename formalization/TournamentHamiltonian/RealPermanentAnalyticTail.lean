import TournamentHamiltonian.ActualPermanentFloorTail

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem normalizedPermanentPolynomial_ofReal (E : Matrix ι ι ℝ) :
    (normalizedPermanentPolynomial E).map Complex.ofRealHom =
      normalizedPermanentPolynomial (Complex.ofRealHom.mapMatrix E) := by
  ext k
  rw [Polynomial.coeff_map, normalizedPermanentPolynomial_coeff,
    normalizedPermanentPolynomial_coeff]
  change Complex.ofRealHom (permanentMinorSum E k / _) =
    permanentMinorSum (fun i j => Complex.ofRealHom (E i j)) k / _
  rw [map_permanentMinorSum, map_div₀, map_natCast]

theorem ofReal_matrix_nat_smul (B : Matrix ι ι ℝ) :
    Complex.ofRealHom.mapMatrix ((Fintype.card ι : ℝ) • B) =
      (Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B := by
  ext i j
  change Complex.ofRealHom ((Fintype.card ι : ℝ) * B i j) =
    (Fintype.card ι : ℂ) * Complex.ofRealHom (B i j)
  rw [map_mul, map_natCast]

theorem real_normalized_permanent_coefficient_bound (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (R q C : ℝ)
    (hR : 0 < R) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hRq : R * q < 1) (k : ℕ) :
    |(normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k| ≤
      Real.exp (R * C * Real.sqrt (Fintype.card ι) / (1 - R * q)) / R ^ k := by
  have h := actual_normalized_permanent_coefficient_bound B hB hp R q C hR hgap hC hF hRq k
  rw [← ofReal_matrix_nat_smul, ← normalizedPermanentPolynomial_ofReal,
    Polynomial.coeff_map] at h
  simpa only [Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs] using h

theorem real_normalized_permanent_floor_tail_bound (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (R q C α : ℝ)
    (hR : 1 < R) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hRq : R * q < 1) :
    (∑ k ∈ (normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).support.filter
        (fun k => Nat.floor (α * Fintype.card ι) < k),
      |(normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k|) ≤
          R / (R - 1) * Real.exp
            (R * C / (1 - R * q) * Real.sqrt (Fintype.card ι) -
              α * Fintype.card ι * Real.log R) := by
  have h := actual_normalized_permanent_floor_tail_bound B hB hp R q C α hR hgap hC hF hRq
  rw [← ofReal_matrix_nat_smul, ← normalizedPermanentPolynomial_ofReal,
    Polynomial.support_map_of_injective _ Complex.ofReal_injective] at h
  simpa only [Polynomial.coeff_map, Complex.ofRealHom_eq_coe, Complex.norm_real,
    Real.norm_eq_abs] using h

end TournamentHamiltonian
