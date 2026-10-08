import TournamentHamiltonian.ActualCoreActivity
import TournamentHamiltonian.CoreActivityPredicate

/-! The activity predicate follows from the actual entry and operator bounds. -/

namespace TournamentHamiltonian

open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable Classical.decEq

variable {ι : Type*} [Fintype ι]

theorem actualCoreActivities_of_matrix_bounds (B : Matrix ι ι ℝ) (C q : ℝ)
    (hn : 0 < Fintype.card ι) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i l, |B i l| ≤ C / (Fintype.card ι : ℝ)) (hZ : ‖B‖ ≤ q) :
    ActualCoreActivities B C q := by
  have hR : 0 ≤ permanentAnalyticRadius q := by
    have h := permanentAnalyticRadius_one_lt q hq hq1
    linarith
  have hgap := permanentAnalyticRadius_gap q hq hq1
  have hW := permanentChainBudget_one_le C q
  have hAW : C * permanentAnalyticRadius q +
      C ^ 2 * permanentAnalyticRadius q ^ 2 / (1 - permanentAnalyticRadius q * q) ≤
      permanentChainBudget C q := le_max_right _ _
  constructor
  · simpa only [permanentFirstExcessBudget] using actualCoreExcessCoefficient_one_window_le B
      (Finset.range (Nat.floor (permanentWindowFraction C q * Fintype.card ι) + 1))
      C q (permanentAnalyticRadius q) (permanentChainBudget C q)
      hC hn hR hentry hZ hgap hAW
  · intro j hj
    have hjpos : 0 < j := by have h := (Finset.mem_Icc.mp hj).1; omega
    simpa only [permanentExcessBudget, excessWindowTerm] using actualCoreExcessCoefficient_activity_le B j hjpos
      (Finset.range (Nat.floor (permanentWindowFraction C q * Fintype.card ι) + 1))
      C q (permanentAnalyticRadius q) (permanentChainBudget C q)
      hC hn hR hentry hZ hgap hW hAW

end TournamentHamiltonian
