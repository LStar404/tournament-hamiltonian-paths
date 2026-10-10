import TournamentHamiltonian.ActualCoreActivity
import TournamentHamiltonian.PermanentApproximationWindow

/-! The actual core budget and normalized permanent window, with no coefficient activity input. -/

namespace TournamentHamiltonian

open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι]

theorem actual_core_abs_window_from_matrix_bounds (B : Matrix ι ι ℝ)
    (M : ℕ) (C q R W : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) (hW : 1 ≤ W)
    (hAW : C * R + C ^ 2 * R ^ 2 / (1 - R * q) ≤ W)
    (hM : 16 * (710 * W ^ 3) * (M : ℝ) ≤ Fintype.card ι) :
    (∑ k ∈ Finset.range (M + 1), coreExcessAbsCoefficient B k * R ^ k) ≤
      ((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) / (Fintype.card ι : ℝ) +
        8 * (710 * W ^ 3) ^ 2 / (Fintype.card ι : ℝ) ^ 2 := by
  have hW0 : 0 ≤ W := by linarith
  apply actual_core_finite_excess_window_le B (Fintype.card ι) M
    (710 * W ^ 3) ((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) R hn (by positivity) hR hM
  · exact actualCoreExcessCoefficient_one_window_le B (Finset.range (M + 1)) C q R W
      hC hn hR hB hq hgap hAW
  · intro j hj
    have hjpos : 0 < j := by have h := (Finset.mem_Icc.mp hj).1; omega
    simpa only [excessWindowTerm, mul_assoc] using
      actualCoreExcessCoefficient_activity_le B j hjpos (Finset.range (M + 1)) C q R W
        hC hn hR hB hq hgap hW hAW

theorem actual_normalized_permanent_window_from_matrix_bounds (B : Matrix ι ι ℝ)
    (hcenter : DoublyCentered B) (hn : 0 < Fintype.card ι) (M : ℕ)
    (Ce Cg q σ R W : ℝ) (hCe : 0 ≤ Ce) (hCg : 0 ≤ Cg)
    (hσ : 1 < σ) (hσR : σ < R) (hRq : R * q < 1)
    (hZ : ‖B‖ ≤ q) (hF : realFrobeniusNorm B ≤ Cg)
    (hentry : ∀ i l, |B i l| ≤ Ce / (Fintype.card ι : ℝ))
    (hW : 1 ≤ W) (hAW : Ce * R + Ce ^ 2 * R ^ 2 / (1 - R * q) ≤ W)
    (hM : 16 * (710 * W ^ 3) * (M : ℝ) ≤ Fintype.card ι)
    (h2M : 2 * M ≤ Fintype.card ι) (hlog : (M : ℝ) / Fintype.card ι ≤ Real.log σ) :
    (∑ k ∈ Finset.range (M + 1),
      |(normalizedPermanentPolynomial ((Fintype.card ι : ℝ) • B)).coeff k -
        bilinearGaussianCoefficient B k|) ≤
      gramGaussian (R • B) *
        ((((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) / (Fintype.card ι : ℝ)) +
          8 * (710 * W ^ 3) ^ 2 / (Fintype.card ι : ℝ) ^ 2) +
        gaussianFactorialRecoveryBudget Cg q σ R / Fintype.card ι := by
  have hq0 : 0 ≤ q := (norm_nonneg B).trans hZ
  have hR : 0 ≤ R := by linarith
  apply actual_normalized_permanent_finite_window_error_le B hcenter hn M Cg q σ R _
    hCg hq0 hσ hσR hRq hZ hF
  · exact actual_core_abs_window_from_matrix_bounds B M Ce q R W hCe hn hR hentry hZ hRq hW hAW hM
  · intro k hk
    have hkM : k ≤ M := by have h := Finset.mem_range.mp hk; omega
    constructor
    · omega
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast hkM) (Nat.cast_nonneg _)).trans hlog

end TournamentHamiltonian
