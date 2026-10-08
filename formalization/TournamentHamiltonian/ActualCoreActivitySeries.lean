import TournamentHamiltonian.ActualCoreActivity
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators Matrix.Norms.L2Operator

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

variable {ι : Type*} [Fintype ι]

/-- The real core series of each fixed positive excess is absolutely
summable. This assertion makes no claim about summation over all excesses. -/
theorem actualCoreExcessCoefficient_weighted_summable (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0 < j) (C q R : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) :
    Summable (fun k => |actualCoreExcessCoefficient B j k| * R ^ k) := by
  apply summable_of_sum_le (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg hR _))
  intro s
  exact actualCoreExcessCoefficient_finite_window_le B j hj s C q R hC hn hR hB hq hgap

/-- The full degree sum in the manuscript's compressed-core activity lemma,
obtained from actual decorated cores and actual matrix contractions. -/
theorem actualCoreExcessCoefficient_tsum_activity_le (B : Matrix ι ι ℝ)
    (j : ℕ) (hj : 0 < j) (C q R W : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1) (hW : 1 ≤ W)
    (hAW : C * R + C ^ 2 * R ^ 2 / (1 - R * q) ≤ W) :
    (∑' k, |actualCoreExcessCoefficient B j k| * R ^ k) ≤
      ((710 * W ^ 3 * (j : ℝ)) / (Fintype.card ι : ℝ)) ^ j := by
  exact (actualCoreExcessCoefficient_weighted_summable B j hj C q R hC hn hR hB hq hgap).tsum_le_of_sum_le
    (fun s => actualCoreExcessCoefficient_activity_le B j hj s C q R W
      hC hn hR hB hq hgap hW hAW)

theorem actualCoreExcessCoefficient_one_tsum_le (B : Matrix ι ι ℝ)
    (C q R W : ℝ)
    (hC : 0 ≤ C) (hn : 0 < Fintype.card ι) (hR : 0 ≤ R)
    (hB : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hq : ‖B‖ ≤ q)
    (hgap : R * q < 1)
    (hAW : C * R + C ^ 2 * R ^ 2 / (1 - R * q) ≤ W) :
    (∑' k, |actualCoreExcessCoefficient B 1 k| * R ^ k) ≤
      ((3 / 2 : ℝ) * W ^ 2 + (10 / 3 : ℝ) * W ^ 3) / (Fintype.card ι : ℝ) := by
  exact (actualCoreExcessCoefficient_weighted_summable B 1 (by omega) C q R hC hn hR hB hq hgap).tsum_le_of_sum_le
    (fun s => actualCoreExcessCoefficient_one_window_le B s C q R W
      hC hn hR hB hq hgap hAW)

end TournamentHamiltonian
