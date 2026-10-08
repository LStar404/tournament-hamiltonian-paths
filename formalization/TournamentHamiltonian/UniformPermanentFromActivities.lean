import TournamentHamiltonian.PermanentAnalyticDefaults
import TournamentHamiltonian.PermanentApproximationRate
import TournamentHamiltonian.PermanentEntryFrobenius

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TournamentHamiltonian

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def uniformPermanentActivityConstant (C q : ℝ) : ℝ :=
  permanentApproximationUniformConstant C q (permanentRecoveryRadius q) (permanentAnalyticRadius q)
    (permanentExcessBudget C q) (permanentFirstExcessBudget C q) (permanentWindowFraction C q)

variable {ι : Type*} [Fintype ι]

theorem DoublyCentered.real_smul (E : Matrix ι ι ℝ) (hE : DoublyCentered E) (c : ℝ) :
    DoublyCentered (c • E) := by
  constructor
  · intro i
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hE.1, mul_zero]
  · intro j
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hE.2, mul_zero]

/-- The manuscript's real-matrix entry point with all analytic constants fixed.
Its only unproved mathematical inputs are displayed as actual graph activity
windows, so this theorem does not assert the unconditional main bound. -/
theorem uniform_permanent_approximation_of_actual_activities (E : Matrix ι ι ℝ)
    (hE : DoublyCentered E) (hp : 0 < Fintype.card ι) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    (hentry : ∀ i j, |E i j| ≤ C)
    (hZ : ‖(Fintype.card ι : ℝ)⁻¹ • E‖ ≤ q)
    (hfirst : (∑ k ∈ Finset.range
      (Nat.floor (permanentWindowFraction C q * Fintype.card ι) + 1),
      |actualCoreExcessCoefficient ((Fintype.card ι : ℝ)⁻¹ • E) 1 k| *
        permanentAnalyticRadius q ^ k) ≤ permanentFirstExcessBudget C q / Fintype.card ι)
    (hexcess : ∀ j ∈ Finset.Icc 2
      (Nat.floor (permanentWindowFraction C q * Fintype.card ι)),
      (∑ k ∈ Finset.range (Nat.floor (permanentWindowFraction C q * Fintype.card ι) + 1),
        |actualCoreExcessCoefficient ((Fintype.card ι : ℝ)⁻¹ • E) j k| *
          permanentAnalyticRadius q ^ k) ≤ excessWindowTerm (permanentExcessBudget C q) (Fintype.card ι) j) :
    |(Matrix.permanent (fun i j => 1 + E i j)) / ((Fintype.card ι).factorial : ℝ) -
        gramGaussian ((Fintype.card ι : ℝ)⁻¹ • E)| ≤
      uniformPermanentActivityConstant C q / Fintype.card ι := by
  have hσ := permanentRecoveryRadius_bounds q hq hq1
  have hα := permanentWindowFraction_pos C q hq hq1
  have hactual := actual_permanent_approximation_of_core_activities
    ((Fintype.card ι : ℝ)⁻¹ • E) (hE.real_smul _ _) hp C q
    (permanentRecoveryRadius q) (permanentAnalyticRadius q) (permanentExcessBudget C q)
    (permanentFirstExcessBudget C q) (permanentWindowFraction C q)
    hC hq hσ.1 hσ.2 (permanentAnalyticRadius_gap q hq hq1) hZ
    (realFrobeniusNorm_normalized_entry_budget E hp C hC hentry)
    (permanentExcessBudget_pos C q).le (permanentFirstExcessBudget_nonneg C q) hα.le
    (permanentWindowFraction_quarter_le C q) (permanentWindowFraction_excess_le C q)
    (permanentWindowFraction_log_le C q hq hq1) hfirst hexcess
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hmat : (fun i j => 1 + (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ)⁻¹ • E) i j) = (fun i j => 1 + E i j) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [hmat] at hactual
  exact hactual.trans (permanentApproximationActivityBudget_le_inverse _ hp C q
    (permanentRecoveryRadius q) (permanentAnalyticRadius q) (permanentExcessBudget C q)
    (permanentFirstExcessBudget C q) (permanentWindowFraction C q)
    hσ.1 (permanentAnalyticRadius_one_lt q hq hq1) hα)

end TournamentHamiltonian
