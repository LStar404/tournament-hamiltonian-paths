import TournamentHamiltonian.UniformPermanentFromActivities

set_option backward.isDefEq.respectTransparency false

namespace TournamentHamiltonian

theorem uniformPermanentActivityConstant_nonneg (C q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ uniformPermanentActivityConstant C q := by
  let σ := permanentRecoveryRadius q
  let R := permanentAnalyticRadius q
  let α := permanentWindowFraction C q
  have hσ := permanentRecoveryRadius_bounds q hq hq1
  have hR := permanentAnalyticRadius_one_lt q hq hq1
  have hα := permanentWindowFraction_pos C q hq hq1
  have hT := permanentFirstExcessBudget_nonneg C q
  have hr0 : 0 ≤ σ / R := div_nonneg (by dsimp [σ]; linarith) (by dsimp [R]; linarith)
  have hr1 : σ / R < 1 := (div_lt_one (by dsimp [R]; linarith)).mpr hσ.2
  have hg : 0 ≤ geometricSecondMoment (σ / R) := by
    unfold geometricSecondMoment
    positivity
  have hrec : 0 ≤ gaussianFactorialRecoveryBudget C q σ R := by
    unfold gaussianFactorialRecoveryBudget
    exact mul_nonneg hg (Real.exp_pos _).le
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hlogσ : 0 < Real.log σ := Real.log_pos hσ.1
  change 0 ≤ permanentApproximationUniformConstant C q σ R
    (permanentExcessBudget C q) (permanentFirstExcessBudget C q) α
  unfold permanentApproximationUniformConstant
  positivity

end TournamentHamiltonian
