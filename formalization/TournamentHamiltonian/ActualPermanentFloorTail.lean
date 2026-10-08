import TournamentHamiltonian.ActualPermanentCircleTail
import TournamentHamiltonian.PolynomialFloorTail

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- Exactly the manuscript's absolute analytic tail term at M=floor(α n),
derived from the genuine permanent and genuine real matrix norm bounds. -/
theorem actual_normalized_permanent_floor_tail_bound (B : Matrix ι ι ℝ)
    (hB : DoublyCentered B) (hp : 0 < Fintype.card ι) (R q C α : ℝ)
    (hR : 1 < R) (hgap : ‖B‖ ≤ q) (hC : 0 ≤ C) (hF : realFrobeniusNorm B ≤ C)
    (hRq : R * q < 1) :
    (∑ k ∈ (normalizedPermanentPolynomial
      ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).support.filter
        (fun k => Nat.floor (α * Fintype.card ι) < k),
      ‖(normalizedPermanentPolynomial
        ((Fintype.card ι : ℂ) • Complex.ofRealHom.mapMatrix B)).coeff k‖) ≤
          R / (R - 1) * Real.exp
            (R * C / (1 - R * q) * Real.sqrt (Fintype.card ι) -
              α * Fintype.card ι * Real.log R) := by
  have h := polynomial_circle_floor_tail_bound _ R
    (R * C * Real.sqrt (Fintype.card ι) / (1 - R * q)) (α * Fintype.card ι) hR
    (actual_normalized_permanent_circle_bound B hB hp R q C hgap hC hF hRq)
  convert h using 1
  congr 2
  ring

end TournamentHamiltonian
