import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Scalar absorption in manuscript §5.4. Establishing the error bound
uniformly over tournament matrices is a separate analytic obligation. -/

namespace TournamentHamiltonian

theorem score_young {τ n K : ℝ} (hτ : 0 ≤ τ) (hn : 0 < n) :
    K * Real.sqrt (τ / n) ≤ τ / 4 + K ^ 2 / n := by
  have hsq : (n * Real.sqrt (τ / n)) ^ 2 = n * τ := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hτ hn.le)]
    field_simp
  have h := sq_nonneg (n * Real.sqrt (τ / n) / 2 - K)
  have hscaled : n * (K * Real.sqrt (τ / n)) ≤ n * (τ / 4 + K ^ 2 / n) := by
    have hcancel : n * (K ^ 2 / n) = K ^ 2 := by field_simp
    rw [mul_add, hcancel]
    nlinarith
  exact (mul_le_mul_iff_right₀ hn).mp (by simpa [mul_comm] using hscaled)

/-- The score penalty dominates a polynomial budget of at most τ/4 and
the square-root error. This lemma does not assume the final path bound. -/
theorem score_penalty_absorption {τ n K err : ℝ}
    (hτ : 0 ≤ τ) (hn : 0 < n) (herr : err ≤ τ / 4) :
    -τ + err + K / n + K * Real.sqrt (τ / n) ≤
      -τ / 2 + (K + K ^ 2) / n := by
  have h := score_young (K := K) hτ hn
  rw [add_div]
  linarith

end TournamentHamiltonian
